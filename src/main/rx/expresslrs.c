/*
 * This file is part of Cleanflight and Betaflight.
 *
 * Cleanflight and Betaflight are free software. You can redistribute
 * this software and/or modify this software under the terms of the
 * GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option)
 * any later version.
 *
 * Cleanflight and Betaflight are distributed in the hope that they
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied
 * warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this software.
 *
 * If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Based on https://github.com/ExpressLRS/ExpressLRS
 * Thanks to AlessandroAU, original creator of the ExpressLRS project.
 *
 * Authors:
 * Phobos- - Original port.
 * Dominic Clifton/Hydra - Timer-based timeout implementation.
 * Phobos- - Port of v2.0
 */

#include <string.h>
#include "platform.h"

#ifdef USE_RX_EXPRESSLRS

#include "build/debug.h"
#include "build/debug_pin.h"

#include "common/maths.h"
#include "common/filter.h"

#include "drivers/io.h"
#include "drivers/rx/rx_spi.h"
#include "drivers/system.h"
#include "drivers/time.h"
#include "drivers/timer.h"
#include "drivers/rx/rx_sx127x.h"
#include "drivers/rx/rx_sx1280.h"
#include "drivers/rx/expresslrs_driver.h"

#include "config/config.h"
#include "config/feature.h"

#include "pg/pg.h"
#include "pg/pg_ids.h"
#include "pg/rx_spi.h"
#include "pg/rx_spi_expresslrs.h"

#include "rx/rx.h"
#include "rx/rx_spi.h"
#include "rx/rx_spi_common.h"

#include "rx/expresslrs.h"
#include "rx/expresslrs_common.h"
#include "rx/expresslrs_impl.h"
#include "rx/expresslrs_telemetry.h"

STATIC_UNIT_TESTED elrsReceiver_t receiver;
static const uint8_t BindingUID[6] = {0,1,2,3,4,5}; // Special binding UID values
static uint16_t crcInitializer = 0;
static uint8_t bindingRateIndex = 0;
static bool connectionHasModelMatch = false;
static uint8_t txPower = 0;
static volatile uint8_t localNonceRx = 0;

static simpleLowpassFilter_t rssiFilter;

static void rssiFilterReset(void)
{
    simpleLPFilterInit(&rssiFilter, 5, 5);
}

#define PACKET_HANDLING_TO_TOCK_ISR_DELAY_US 250

//
// Event pair recorder
//

typedef enum {
    EPR_FIRST,
    EPR_SECOND,
} eprEvent_e;

#define EPR_EVENT_COUNT 2

typedef struct eprState_s {
    uint32_t eventAtUs[EPR_EVENT_COUNT];
    bool eventRecorded[EPR_EVENT_COUNT];
} eprState_t;

eprState_t eprState = {0};

static void expressLrsEPRRecordEvent(eprEvent_e event, uint32_t currentTimeUs)
{
    eprState.eventAtUs[event] = currentTimeUs;
    eprState.eventRecorded[event] = true;
}

static bool expressLrsEPRHaveBothEvents(void)
{
    bool bothEventsRecorded = eprState.eventRecorded[EPR_SECOND] && eprState.eventRecorded[EPR_FIRST];
    return bothEventsRecorded;
}

static int32_t expressLrsEPRGetResult(void)
{
    if (!expressLrsEPRHaveBothEvents()) {
        return 0;
    }

    return (int32_t)(eprState.eventAtUs[EPR_SECOND] - eprState.eventAtUs[EPR_FIRST]);
}

static void expressLrsEPRReset(void)
{
    memset(&eprState, 0, sizeof(eprState_t));
}


//
// Phase Lock
//


#define EPR_INTERNAL EPR_FIRST
#define EPR_EXTERNAL EPR_SECOND

typedef struct phaseLockState_s {
    simpleLowpassFilter_t offsetFilter;
    simpleLowpassFilter_t offsetDxFilter;

    int32_t rawOffsetUs;
    int32_t previousRawOffsetUs;

    int32_t offsetUs;
    int32_t offsetDeltaUs;
    int32_t previousOffsetUs;
} phaseLockState_t;

static phaseLockState_t pl;

static void expressLrsPhaseLockReset(void)
{
    simpleLPFilterInit(&pl.offsetFilter, 2, 5);
    simpleLPFilterInit(&pl.offsetDxFilter, 4, 5);

    expressLrsEPRReset();
}

static uint8_t nextTelemetryType = ELRS_TELEMETRY_TYPE_LINK;

static uint8_t telemetryBurstCount = 1;
static uint8_t telemetryBurstMax = 1;
static bool telemBurstValid = false;

// Maximum ms between LINK_STATISTICS packets for determining burst max
#define TELEM_MIN_LINK_INTERVAL 512U

#ifdef USE_MSP_OVER_TELEMETRY
static uint8_t mspBuffer[ELRS_MSP_BUFFER_SIZE];
#endif

//
// Stick unpacking
//

static void setRssiChannelData(uint16_t *rcData)
{
    rcData[ELRS_LQ_CHANNEL] = scaleRange(receiver.uplinkLQ, 0, 100, 988, 2011);
    rcData[ELRS_RSSI_CHANNEL] = scaleRange(constrain(receiver.rssiFiltered, receiver.rf_perf_params->sensitivity, -50), receiver.rf_perf_params->sensitivity, -50, 988, 2011); 
}

static void unpackAnalogChannelData(uint16_t *rcData, const uint8_t *payload)
{
    rcData[0] = convertAnalog((payload[0] << 3) | ((payload[4] & 0xC0) >> 5));
    rcData[1] = convertAnalog((payload[1] << 3) | ((payload[4] & 0x30) >> 3));
    rcData[2] = convertAnalog((payload[2] << 3) | ((payload[4] & 0x0C) >> 1));
    rcData[3] = convertAnalog((payload[3] << 3) | ((payload[4] & 0x03) << 1));
}

/**
 * Hybrid switches uses 10 bits for each analog channel,
 * 2 bits for the low latency switch[0]
 * 3 bits for the round-robin switch index and 2 bits for the value
 * 4 analog channels, 1 low latency switch and round robin switch data = 47 bits (1 free)
 * 
 * sets telemetry status bit
 */
static void unpackChannelDataHybridSwitch8(uint16_t *rcData, const uint8_t *payload)
{
    unpackAnalogChannelData(rcData, payload);

    const uint8_t switchByte = payload[5];

    // The low latency switch
    rcData[4] = convertSwitch1b((switchByte & 0x40) >> 6);

    // The round-robin switch, switchIndex is actually index-1 
    // to leave the low bit open for switch 7 (sent as 0b11x)
    // where x is the high bit of switch 7
    uint8_t switchIndex = (switchByte & 0x38) >> 3;
    uint16_t switchValue = convertSwitch3b(switchByte & 0x07);

    switch (switchIndex) {
        case 0:
            rcData[5] = switchValue;
            break;
        case 1:
            rcData[6] = switchValue;
            break;
        case 2:
            rcData[7] = switchValue;
            break;
        case 3:
            rcData[8] = switchValue;
            break;
        case 4:
            rcData[9] = switchValue;
            break;
        case 5:
            rcData[10] = switchValue;
            break;
        case 6:
            FALLTHROUGH;
        case 7:
            rcData[11] = convertSwitchNb(switchByte & 0x0F, 15); //4-bit
            break;
        default:
            break;
    }

    setRssiChannelData(rcData);

    // TelemetryStatus bit
    confirmCurrentTelemetryPayload(switchByte & (1 << 7));
}

/**
 * HybridWide switches decoding of over the air data
 *
 * Hybrid switches uses 10 bits for each analog channel,
 * 1 bits for the low latency switch[0]
 * 6 or 7 bits for the round-robin switch
 * 1 bit for the TelemetryStatus, which may be in every packet or just idx 7
 * depending on TelemetryRatio
 *
 * Output: crsf.PackedRCdataOut, crsf.LinkStatistics.uplink_TX_Power
 * Returns: TelemetryStatus bit
 */
static void unpackChannelDataHybridWide(uint16_t *rcData, const uint8_t *payload)
{
    unpackAnalogChannelData(rcData, payload);
    const uint8_t switchByte = payload[5];

    // The low latency switch
    rcData[4] = convertSwitch1b((switchByte & 0x80) >> 7);

    // The round-robin switch, 6-7 bits with the switch index implied by the nonce
    uint8_t switchIndex = hybridWideNonceToSwitchIndex(localNonceRx);
    bool telemInEveryPacket = (tlmRatioEnumToValue(receiver.mod_params->tlmInterval) < 8);
    if (telemInEveryPacket || switchIndex == 7) {
        confirmCurrentTelemetryPayload((switchByte & 0x40) >> 6);
    }
    if (switchIndex >= 7) {
        txPower = switchByte & 0x3F;
    } else {
        uint8_t bins;
        uint16_t switchValue;
        if (telemInEveryPacket) {
            bins = 63;
            switchValue = switchByte & 0x3F; // 6-bit
        } else {
            bins = 127;
            switchValue = switchByte & 0x7F; // 7-bit
        }

        switchValue = convertSwitchNb(switchValue, bins);
        rcData[5 + switchIndex] = switchValue;
    }

    setRssiChannelData(rcData);
}

static void startReceiving(void)
{
    dbgPinLo(1);
    receiver.startReceiving();
}

static uint8_t minLqForChaos(void)
{
    // Determine the most number of CRC-passing packets we could receive on
    // a single channel out of 100 packets that fill the LQcalc span.
    // The LQ must be GREATER THAN this value, not >=
    // The amount of time we coexist on the same channel is
    // 100 divided by the total number of packets in a FHSS loop (rounded up)
    // and there would be 4x packets received each time it passes by so
    // FHSShopInterval * ceil(100 / FHSShopInterval * numfhss) or
    // FHSShopInterval * trunc((100 + (FHSShopInterval * numfhss) - 1) / (FHSShopInterval * numfhss))
    // With a interval of 4 this works out to: 2.4=4, FCC915=4, AU915=8, EU868=8, EU/AU433=36
    const uint32_t numfhss = getFHSSNumEntries();
    const uint8_t interval = receiver.mod_params->fhssHopInterval;
    return interval * ((interval * numfhss + 99) / (interval * numfhss));
}

static void setRFLinkRate(const uint8_t index)
{
#if defined(USE_RX_SX1280) && defined(USE_RX_SX127X)
    receiver.mod_params = (rxExpressLrsSpiConfig()->domain == ISM2400) ? &air_rate_config[1][index] : &air_rate_config[0][index];
    receiver.rf_perf_params = (rxExpressLrsSpiConfig()->domain == ISM2400) ? &rf_perf_config[1][index] : &rf_perf_config[0][index];
#else
    receiver.mod_params = &air_rate_config[0][index];
    receiver.rf_perf_params = &rf_perf_config[0][index];
#endif
    receiver.currentFreq = getInitialFreq(receiver.freqOffset);
    // Wait for (11/10) 110% of time it takes to cycle through all freqs in FHSS table (in ms)
    receiver.cycleIntervalMs = ((uint32_t)11U * getFHSSNumEntries() * receiver.mod_params->fhssHopInterval * receiver.mod_params->interval) / (10U * 1000U);

    receiver.config(receiver.mod_params->bw, receiver.mod_params->sf, receiver.mod_params->cr, receiver.currentFreq, receiver.mod_params->preambleLen, receiver.UID[5] & 0x01);

    expressLrsUpdateTimerInterval(receiver.mod_params->interval);

    rssiFilterReset();
    receiver.nextRateIndex = index; // presumably we just handled this
    telemBurstValid = false;
}

static bool handleFHSS(void)
{
    uint8_t modresultFHSS = (receiver.nonceRX + 1) % receiver.mod_params->fhssHopInterval;

    if ((receiver.mod_params->fhssHopInterval == 0) || receiver.alreadyFHSS == true || receiver.inBindingMode || (modresultFHSS != 0) || (receiver.connectionState == DISCONNECTED)) {
        return false;
    }

    receiver.alreadyFHSS = true;
    receiver.currentFreq = FHSSgetNextFreq(receiver.freqOffset);
    receiver.setFrequency(receiver.currentFreq);

    uint8_t modresultTLM = (receiver.nonceRX + 1) % (tlmRatioEnumToValue(receiver.mod_params->tlmInterval));

    if (modresultTLM != 0 || receiver.mod_params->tlmInterval == TLM_RATIO_NO_TLM) { // if we are about to send a tlm response don't bother going back to rx
        startReceiving();
    }
    return true;
}

static bool handleSendTelemetryResponse(void)
{
    uint8_t packet[8];

    uint8_t *data;
    uint8_t maxLength;
    uint8_t packageIndex;
    uint8_t modresult = (receiver.nonceRX + 1) % tlmRatioEnumToValue(receiver.mod_params->tlmInterval);

    if ((receiver.connectionState == DISCONNECTED) || (receiver.mod_params->tlmInterval == TLM_RATIO_NO_TLM) || (receiver.alreadyTLMresp == true) || (modresult != 0))
    {
        return false; // don't bother sending tlm if disconnected or TLM is off
    }

    receiver.alreadyTLMresp = true;
    packet[0] = ELRS_TLM_PACKET;

    if (nextTelemetryType == ELRS_TELEMETRY_TYPE_LINK || !isTelemetrySenderActive()) {
        packet[1] = ELRS_TELEMETRY_TYPE_LINK;
        packet[2] = receiver.rssiFiltered; //diversity not supported
        packet[3] = connectionHasModelMatch << 7;
        packet[4] = receiver.snr;
        packet[5] = receiver.uplinkLQ;
#ifdef USE_MSP_OVER_TELEMETRY
        packet[6] = getCurrentMspConfirm() ? 1 : 0;
#else
        packet[6] = 0;
#endif
        nextTelemetryType = ELRS_TELEMETRY_TYPE_DATA;
        // Start the count at 1 because the next will be DATA and doing +1 before checking
        // against Max below is for some reason 10 bytes more code
        telemetryBurstCount = 1;
    } else {
        if (telemetryBurstCount < telemetryBurstMax) {
            telemetryBurstCount++;
        } else {
            nextTelemetryType = ELRS_TELEMETRY_TYPE_LINK;
        }

        getCurrentTelemetryPayload(&packageIndex, &maxLength, &data);
        packet[1] = (packageIndex << ELRS_TELEMETRY_SHIFT) + ELRS_TELEMETRY_TYPE_DATA;
        packet[2] = maxLength > 0 ? *data : 0;
        packet[3] = maxLength >= 1 ? *(data + 1) : 0;
        packet[4] = maxLength >= 2 ? *(data + 2) : 0;
        packet[5] = maxLength >= 3 ? *(data + 3) : 0;
        packet[6] = maxLength >= 4 ? *(data + 4) : 0;
    }

    uint16_t crc = calcCrc14(packet, 7, crcInitializer);
    packet[0] |= (crc >> 6) & 0xFC;
    packet[7] = crc & 0xFF;

    dbgPinHi(1);
    receiver.transmitData(packet, ELRS_RX_TX_BUFF_SIZE);
    return true;
}

static void updatePhaseLock(void)
{
    if (receiver.connectionState != DISCONNECTED && expressLrsEPRHaveBothEvents()) {
        pl.rawOffsetUs = expressLrsEPRGetResult();

        pl.offsetUs = simpleLPFilterUpdate(&pl.offsetFilter, pl.rawOffsetUs);
        pl.offsetDeltaUs = simpleLPFilterUpdate(&pl.offsetDxFilter, pl.rawOffsetUs - pl.previousRawOffsetUs);

        if (receiver.timerState == TIM_LOCKED && lqPeriodIsSet())
        {
            if (receiver.nonceRX % 8 == 0) //limit rate of freq offset adjustment slightly
            {
                if (pl.offsetUs > 0)
                {
                    expressLrsTimerIncreaseFrequencyOffset();
                }
                else if (pl.offsetUs < 0)
                {
                    expressLrsTimerDecreaseFrequencyOffset();
                }
            }
        }

        if (receiver.connectionState != CONNECTED)
        {
            expressLrsUpdatePhaseShift(pl.rawOffsetUs >> 1);
        }
        else
        {
            expressLrsUpdatePhaseShift(pl.offsetUs >> 2);
        }

        pl.previousOffsetUs = pl.offsetUs;
        pl.previousRawOffsetUs = pl.rawOffsetUs;

        expressLrsTimerDebug();

        DEBUG_SET(DEBUG_RX_EXPRESSLRS_PHASELOCK, 0, pl.rawOffsetUs);
        DEBUG_SET(DEBUG_RX_EXPRESSLRS_PHASELOCK, 1, pl.offsetUs);
    }

    expressLrsEPRReset();
}

//hwTimerCallbackTick
void expressLrsOnTimerTickISR(void) // this is 180 out of phase with the other callback, occurs mid-packet reception
{
    updatePhaseLock();
    receiver.nonceRX += 1;

    // if (!alreadyTLMresp && !alreadyFHSS && !LQCalc.currentIsSet()) // packet timeout AND didn't DIDN'T just hop or send TLM
    // {
    //     Radio.RXnb(); // put the radio cleanly back into RX in case of garbage data
    // }

    // Save the LQ value before the inc() reduces it by 1
    receiver.uplinkLQ = lqGet();
    // Only advance the LQI period counter if we didn't send Telemetry this period
    if (!receiver.alreadyTLMresp) {
        lqNewPeriod();
    }

    receiver.alreadyTLMresp = false;
    receiver.alreadyFHSS = false;
}

//hwTimerCallbackTock
void expressLrsOnTimerTockISR(void)
{
    uint32_t currentTimeUs = micros();

    expressLrsEPRRecordEvent(EPR_INTERNAL, currentTimeUs);

    receiver.fhssRequired = true; //Rest of the code is moved to expressLrsDataReceived to avoid race condition
}

void lostConnection(void)
{
    receiver.rfModeCycleMultiplier = 1;
    receiver.connectionState = DISCONNECTED; //set lost connection
    receiver.timerState = TIM_DISCONNECTED;
    expressLrsTimerResetFrequencyOffset();
    receiver.freqOffset = 0;
    pl.offsetUs = 0;
    pl.offsetDeltaUs = 0;
    pl.rawOffsetUs = 0;
    pl.previousRawOffsetUs = 0;
    receiver.gotConnectionMs = 0;
    receiver.uplinkLQ = 0;
    lqReset();
    expressLrsPhaseLockReset();
    receiver.alreadyTLMresp = false;
    receiver.alreadyFHSS = false;

    if (!receiver.inBindingMode)
    {
        //while (micros() - expressLrsEPRGetResult() > 250); // time it just after the tock() TODO this currently breaks and is blocking, not a fan of this.
        expressLrsTimerStop();
        setRFLinkRate(receiver.nextRateIndex); // also sets to initialFreq
        startReceiving();
    }
}

static void tentativeConnection(const uint32_t timeStampMs)
{
    receiver.connectionState = TENTATIVE;
    connectionHasModelMatch = false;
    receiver.timerState = TIM_DISCONNECTED;
    receiver.freqOffset = 0;
    pl.offsetUs = 0;
    pl.previousRawOffsetUs = 0;
    expressLrsPhaseLockReset(); //also resets PFD
    receiver.rfModeCycledAtMs = timeStampMs; // give another 3 sec for lock to occur

    // The caller MUST call hwTimer.resume(). It is not done here because
    // the timer ISR will fire immediately and preempt any other code
}

static void gotConnection(const uint32_t timeStampMs)
{
    if (receiver.connectionState == CONNECTED) {
        return; // Already connected
    }

    receiver.lockRFmode = true; // currently works as if LOCK_ON_FIRST_CONNECTION was enabled

    receiver.connectionState = CONNECTED; //we got a packet, therefore no lost connection
    receiver.timerState = TIM_TENTATIVE;
    receiver.gotConnectionMs = timeStampMs;
}

//setup radio
static void initializeReceiver(void)
{
    FHSSrandomiseFHSSsequence(receiver.UID, rxExpressLrsSpiConfig()->domain);
    lqReset();
    receiver.nonceRX = 0;
    receiver.freqOffset = 0;
    receiver.configChanged = false;
    receiver.rssi = 0;
    receiver.rssiFiltered = 0;
    receiver.snr = 0;
    receiver.uplinkLQ = 0;
    receiver.rateIndex = rxExpressLrsSpiConfig()->rateIndex;
    receiver.nextRateIndex = receiver.rateIndex;
    setRFLinkRate(receiver.rateIndex);

    receiver.alreadyFHSS = false;
    receiver.alreadyTLMresp = false;
    receiver.lockRFmode = false;
    receiver.timerState = TIM_DISCONNECTED;
    receiver.connectionState = DISCONNECTED;

    receiver.rfModeCycledAtMs = 0;
    receiver.configCheckedAtMs = 0;
    receiver.statsUpdatedAtMs = 0;
    receiver.gotConnectionMs = 0;
    receiver.lastSyncPacketMs = 0;
    receiver.lastValidPacketMs = 0;

    receiver.rfModeCycleMultiplier = 1;
}

static void unpackBindPacket(uint8_t *packet)
{
    rxExpressLrsSpiConfigMutable()->UID[2] = packet[3];
    rxExpressLrsSpiConfigMutable()->UID[3] = packet[4];
    rxExpressLrsSpiConfigMutable()->UID[4] = packet[5];
    rxExpressLrsSpiConfigMutable()->UID[5] = packet[6];

    receiver.UID = rxExpressLrsSpiConfigMutable()->UID;
    crcInitializer = (receiver.UID[4] << 8) | receiver.UID[5];
    receiver.inBindingMode = false;

    initializeReceiver();

    receiver.configChanged = true; //after initialize as it sets it to false
    startReceiving();
}

/**
 * Process the assembled MSP packet in mspBuffer[]
 **/
static void processRFMspPacket(uint8_t *packet)
{
    // Always examine MSP packets for bind information if in bind mode
    // [1] is the package index, first packet of the MSP
    if (receiver.inBindingMode && packet[1] == 1 && packet[2] == ELRS_MSP_BIND) {
        unpackBindPacket(packet); //onELRSBindMSP
        return;
    }

#ifdef USE_MSP_OVER_TELEMETRY
    // Must be fully connected to process MSP, prevents processing MSP
    // during sync, where packets can be received before connection
    if (receiver.connectionState != CONNECTED) {
        return;
    }

    bool currentMspConfirmValue = getCurrentMspConfirm();
    receiveMspData(packet[1], packet + 2);
    if (currentMspConfirmValue != getCurrentMspConfirm()) {
        nextTelemetryType = ELRS_TELEMETRY_TYPE_LINK;
    }
    if (hasFinishedMspData()) {
        if (mspBuffer[7] == ELRS_MSP_SET_RX_CONFIG && mspBuffer[8] == ELRS_MSP_MODEL_ID) { //mspReceiverComplete
            if (rxExpressLrsSpiConfig()->modelId != mspBuffer[9]) { //UpdateModelMatch
                rxExpressLrsSpiConfigMutable()->modelId = mspBuffer[9];
                receiver.configChanged = true;
                receiver.connectionState = DISCONNECT_PENDING;
            }
        } else if (connectionHasModelMatch) {
            processMspPacket(mspBuffer);
        }

        mspReceiverUnlock();
    }
#endif
}

static bool processRFSyncPacket(uint8_t *packet, const uint32_t timeStampMs)
{
    // Verify the first two of three bytes of the binding ID, which should always match
    if (packet[4] != receiver.UID[3] || packet[5] != receiver.UID[4]) {
        return false;
    }

    // The third byte will be XORed with inverse of the ModelId if ModelMatch is on
    // Only require the first 18 bits of the UID to match to establish a connection
    // but the last 6 bits must modelmatch before sending any data to the FC
    if ((packet[6] & ~ELRS_MODELMATCH_MASK) != (receiver.UID[5] & ~ELRS_MODELMATCH_MASK)) {
        return false;
    }

    receiver.lastSyncPacketMs = timeStampMs;

    // Will change the packet air rate in loop() if this changes
    receiver.nextRateIndex = (packet[3] & 0xC0) >> 6;
    uint8_t tlmRateIn = (packet[3] & 0x38) >> 3;
    uint8_t switchEncMode = ((packet[3] & 0x06) >> 1) - 1; //spi implementation uses 0 based index for hybrid

    // Update switch mode encoding immediately
    if (switchEncMode != rxExpressLrsSpiConfig()->switchMode) {
        rxExpressLrsSpiConfigMutable()->switchMode = switchEncMode;
        receiver.configChanged = true;
    }

    // Update TLM ratio
    if (receiver.mod_params->tlmInterval != tlmRateIn) {
        receiver.mod_params->tlmInterval = tlmRateIn;
        telemBurstValid = false;
    }

    // modelId = 0xff indicates modelMatch is disabled, the XOR does nothing in that case
    uint8_t modelXor = (~rxExpressLrsSpiConfig()->modelId) & ELRS_MODELMATCH_MASK;
    bool modelMatched = packet[6] == (receiver.UID[5] ^ modelXor);

    if (receiver.connectionState == DISCONNECTED || receiver.nonceRX != packet[2] || FHSSgetCurrIndex() != packet[1] || connectionHasModelMatch != modelMatched) {
        FHSSsetCurrIndex(packet[1]);
        receiver.nonceRX = packet[2];

        tentativeConnection(timeStampMs);
        connectionHasModelMatch = modelMatched;

        if (!expressLrsTimerIsRunning()) {
            return true;
        }
    }

    return false;
}

static rx_spi_received_e processRFPacket(uint8_t *payload)
{
    uint8_t packet[ELRS_RX_TX_BUFF_SIZE];

    receiver.receiveData(packet, ELRS_RX_TX_BUFF_SIZE);

    uint32_t timeStampUs = micros();

    elrs_packet_type_e type = packet[0] & 0x03;
    uint16_t inCRC = (((uint16_t)(packet[0] & 0xFC)) << 6 ) | packet[7];

    // For SM_HYBRID the CRC only has the packet type in byte 0
    // For SM_HYBRID_WIDE the FHSS slot is added to the CRC in byte 0 on RC_DATA_PACKETs
    if (type != ELRS_RC_DATA_PACKET || rxExpressLrsSpiConfig()->switchMode != SM_HYBRID_WIDE) {
        packet[0] = type;
    } else {
        uint8_t nonceFHSSresult = receiver.nonceRX % receiver.mod_params->fhssHopInterval;
        packet[0] = type | (nonceFHSSresult << 2);
    }
    uint16_t calculatedCRC = calcCrc14(packet, 7, crcInitializer);

    if (inCRC != calculatedCRC) {
        return RX_SPI_RECEIVED_NONE;
    }

    expressLrsEPRRecordEvent(EPR_EXTERNAL, timeStampUs + PACKET_HANDLING_TO_TOCK_ISR_DELAY_US);

    bool shouldStartTimer = false;
    uint32_t timeStampMs = millis();

    receiver.lastValidPacketMs = timeStampMs;

    switch(type) {
        case ELRS_RC_DATA_PACKET:
            // Must be fully connected to process RC packets, prevents processing RC
            // during sync, where packets can be received before connection
            if (receiver.connectionState == CONNECTED && connectionHasModelMatch) {
                localNonceRx = receiver.nonceRX; // to avoid race condition in hybrid switch code
                memcpy(payload, &packet[1], 6); // tlm confirm code should be here - moved directly to unpacking methods
            }
            break;
        case ELRS_MSP_DATA_PACKET:
            processRFMspPacket(packet);
            break;
        case ELRS_TLM_PACKET:
            //not implemented
            break;
        case ELRS_SYNC_PACKET:
            shouldStartTimer = processRFSyncPacket(packet, timeStampMs) && !receiver.inBindingMode;
            break;
        default:
            return RX_SPI_RECEIVED_NONE;
    }

    // Store the LQ/RSSI/Antenna
    receiver.getRFlinkInfo(&receiver.rssi, &receiver.snr);
    // Received a packet, that's the definition of LQ
    lqIncrease();
    // Extend sync duration since we've received a packet at this rate
    // but do not extend it indefinitely
    receiver.rfModeCycleMultiplier = ELRS_MODE_CYCLE_MULTIPLIER_SLOW; //RFModeCycleMultiplierSlow

    if (shouldStartTimer) {
        expressLrsTimerResume();
    }

    return RX_SPI_RECEIVED_DATA;
}

static void updateTelemetryBurst(void)
{
    if (telemBurstValid) {
        return;
    }
    telemBurstValid = true;

    uint32_t hz = rateEnumToHz(receiver.mod_params->enumRate);
    uint32_t ratiodiv = tlmRatioEnumToValue(receiver.mod_params->tlmInterval);
    // telemInterval = 1000 / (hz / ratiodiv);
    // burst = TELEM_MIN_LINK_INTERVAL / telemInterval;
    // This ^^^ rearranged to preserve precision vvv
    telemetryBurstMax = TELEM_MIN_LINK_INTERVAL * hz / ratiodiv / 1000U;

    // Reserve one slot for LINK telemetry
    if (telemetryBurstMax > 1) {
        --telemetryBurstMax;
    } else {
        telemetryBurstMax = 1;
    }

    // Notify the sender to adjust its expected throughput
    updateTelemetryRate(hz, ratiodiv, telemetryBurstMax);
}

/* If not connected will rotate through the RF modes looking for sync
 * and blink LED
 */
static void cycleRfMode(const uint32_t timeStampMs)
{
    if (receiver.connectionState == CONNECTED || receiver.inBindingMode) {
        return;
    }
    // Actually cycle the RF mode if not LOCK_ON_FIRST_CONNECTION
    if (receiver.lockRFmode == false && (timeStampMs - receiver.rfModeCycledAtMs) > (receiver.cycleIntervalMs * receiver.rfModeCycleMultiplier))
    {
        receiver.rfModeCycledAtMs = timeStampMs;
        receiver.lastSyncPacketMs = timeStampMs;           // reset this variable
        receiver.rateIndex = (receiver.rateIndex + 1) % ELRS_RATE_MAX;
        setRFLinkRate(receiver.rateIndex); // switch between rates
        receiver.statsUpdatedAtMs = timeStampMs;
        lqReset();
        startReceiving();

        // Switch to FAST_SYNC if not already in it (won't be if was just connected)
        receiver.rfModeCycleMultiplier = 1;
    } // if time to switch RF mode
}

#ifdef USE_RX_SX1280
static inline void configureReceiverForSX1280(void)
{
    receiver.init = (elrsRxInitFnPtr) sx1280Init;
    receiver.config = (elrsRxConfigFnPtr) sx1280Config;
    receiver.startReceiving = (elrsRxStartReceivingFnPtr) sx1280StartReceiving;
    receiver.rxISR = (elrsRxISRFnPtr) sx1280ISR;
    receiver.transmitData = (elrsRxTransmitDataFnPtr) sx1280TransmitData;
    receiver.receiveData = (elrsRxReceiveDataFnPtr) sx1280ReceiveData;
    receiver.getRFlinkInfo = (elrsRxGetRFlinkInfoFnPtr) sx1280GetLastPacketStats;
    receiver.setFrequency = (elrsRxSetFrequencyFnPtr) sx1280SetFrequencyReg;
    receiver.handleFreqCorrection = (elrsRxHandleFreqCorrectionFnPtr) sx1280AdjustFrequency;
}
#endif

#ifdef USE_RX_SX127X

static inline void configureReceiverForSX127x(void)
{
    receiver.init = (elrsRxInitFnPtr) sx127xInit;
    receiver.config = (elrsRxConfigFnPtr) sx127xConfig;
    receiver.startReceiving = (elrsRxStartReceivingFnPtr) sx127xStartReceiving;
    receiver.rxISR = (elrsRxISRFnPtr) sx127xISR;
    receiver.transmitData = (elrsRxTransmitDataFnPtr) sx127xTransmitData;
    receiver.receiveData = (elrsRxReceiveDataFnPtr) sx127xReceiveData;
    receiver.getRFlinkInfo = (elrsRxGetRFlinkInfoFnPtr) sx127xGetLastPacketStats;
    receiver.setFrequency = (elrsRxSetFrequencyFnPtr) sx127xSetFrequencyReg;
    receiver.handleFreqCorrection = (elrsRxHandleFreqCorrectionFnPtr) sx127xAdjustFrequency;
}
#endif

//setup
bool expressLrsSpiInit(const struct rxSpiConfig_s *rxConfig, struct rxRuntimeState_s *rxRuntimeState, rxSpiExtiConfig_t *extiConfig)
{
    if (!rxSpiExtiConfigured()) {
        return false;
    }

    rxSpiCommonIOInit(rxConfig);
	
    rxRuntimeState->channelCount = ELRS_MAX_CHANNELS;
	
    extiConfig->ioConfig = IOCFG_IPD;
    extiConfig->trigger = BETAFLIGHT_EXTI_TRIGGER_RISING;

    if (rxExpressLrsSpiConfig()->resetIoTag) {
        receiver.resetPin = IOGetByTag(rxExpressLrsSpiConfig()->resetIoTag);
	} else {
        receiver.resetPin = IO_NONE;
    }

    if (rxExpressLrsSpiConfig()->busyIoTag) {
        receiver.busyPin = IOGetByTag(rxExpressLrsSpiConfig()->busyIoTag);
    } else {
        receiver.busyPin = IO_NONE;
    }

    switch (rxExpressLrsSpiConfig()->domain) {
#ifdef USE_RX_SX127X
        case AU433:
            FALLTHROUGH;
        case AU915:
            FALLTHROUGH;
        case EU433:
            FALLTHROUGH;
        case EU868:
            FALLTHROUGH;
        case IN866:
            FALLTHROUGH;
        case FCC915:
            configureReceiverForSX127x();
            bindingRateIndex = ELRS_BINDING_RATE_900;
            break;
#endif
#ifdef USE_RX_SX1280
        case ISM2400:
            configureReceiverForSX1280();
            bindingRateIndex = ELRS_BINDING_RATE_24;
            break;
#endif
        default:
            return false;
    }

    if (!receiver.init(receiver.resetPin, receiver.busyPin)) {
        return false;
    }

    if (rssiSource == RSSI_SOURCE_NONE) {
        rssiSource = RSSI_SOURCE_RX_PROTOCOL;
    }

    if (linkQualitySource == LQ_SOURCE_NONE) {
        linkQualitySource = LQ_SOURCE_RX_PROTOCOL_CRSF;
    }

    if (rxExpressLrsSpiConfig()->UID[0] || rxExpressLrsSpiConfig()->UID[1]
        || rxExpressLrsSpiConfig()->UID[2] || rxExpressLrsSpiConfig()->UID[3]
        || rxExpressLrsSpiConfig()->UID[4] || rxExpressLrsSpiConfig()->UID[5]) {
        receiver.inBindingMode = false;
        receiver.UID = rxExpressLrsSpiConfig()->UID;
        crcInitializer = (receiver.UID[4] << 8) | receiver.UID[5];
    } else {
        receiver.inBindingMode = true;
        receiver.UID = BindingUID;
        crcInitializer = 0;
        rxExpressLrsSpiConfigMutable()->rateIndex = bindingRateIndex;
    }

    expressLrsPhaseLockReset();

    expressLrsInitialiseTimer(RX_EXPRESSLRS_TIMER_INSTANCE, &receiver.timerUpdateCb);
    expressLrsTimerStop();

    generateCrc14Table();
    initializeReceiver();

    initTelemetry();
#ifdef USE_MSP_OVER_TELEMETRY
    setMspDataToReceive(ELRS_MSP_BUFFER_SIZE, mspBuffer, ELRS_MSP_BYTES_PER_CALL);
#endif

    // Timer IRQs must only be enabled after the receiver is configured otherwise race conditions occur.
    expressLrsTimerEnableIRQs();

    startReceiving();

    return true;
}

static void handleConnectionStateUpdate(const uint32_t timeStampMs)
{
    if ((receiver.connectionState != DISCONNECTED) && (receiver.mod_params->index != receiver.nextRateIndex)) {  // forced change
        lostConnection();
        receiver.lastSyncPacketMs = timeStampMs;                    // reset this variable to stop rf mode switching and add extra time
        receiver.rfModeCycledAtMs = timeStampMs;         // reset this variable to stop rf mode switching and add extra time
        setRssiDirect(0, RSSI_SOURCE_RX_PROTOCOL);
#ifdef USE_RX_RSSI_DBM
        setRssiDbmDirect(-130, RSSI_SOURCE_RX_PROTOCOL);
#endif
#ifdef USE_RX_LINK_QUALITY_INFO
        setLinkQualityDirect(0);
#endif
    }

    if (receiver.connectionState == TENTATIVE && ((timeStampMs - receiver.lastSyncPacketMs) > receiver.rf_perf_params->rxLockTimeoutMs)) {
        lostConnection();
        receiver.rfModeCycledAtMs = timeStampMs;
        receiver.lastSyncPacketMs = timeStampMs;
    }

    cycleRfMode(timeStampMs);

    uint32_t localLastValidPacket = receiver.lastValidPacketMs; // Required to prevent race condition due to LastValidPacket getting updated from ISR
    if ((receiver.connectionState == DISCONNECT_PENDING) || // check if we lost conn.
        ((receiver.connectionState == CONNECTED) && ((int32_t)receiver.rf_perf_params->disconnectTimeoutMs < (int32_t)(timeStampMs - localLastValidPacket)))) {
        lostConnection();
    }

    if ((receiver.connectionState == TENTATIVE) && (ABS(pl.offsetDeltaUs) <= 10) && (pl.offsetUs < 100) && (lqGet() > minLqForChaos())) { //detects when we are connected
        gotConnection(timeStampMs);
    }

    if ((receiver.timerState == TIM_TENTATIVE) && ((timeStampMs - receiver.gotConnectionMs) > ELRS_CONSIDER_CONNECTION_GOOD_MS) && (ABS(pl.offsetDeltaUs) <= 5)) {
        receiver.timerState = TIM_LOCKED;
    }
}

static void handleConfigUpdate(const uint32_t timeStampMs)
{
    if ((timeStampMs - receiver.configCheckedAtMs) > ELRS_CONFIG_CHECK_MS) {
        receiver.configCheckedAtMs = timeStampMs;
        if (receiver.configChanged) {
            writeEEPROM();
            receiver.configChanged = false;
        }
    }
}

static void handleLinkStatsUpdate(const uint32_t timeStampMs)
{
    if ((timeStampMs - receiver.statsUpdatedAtMs) > ELRS_LINK_STATS_CHECK_MS) {

        receiver.statsUpdatedAtMs = timeStampMs;

        if (receiver.connectionState != CONNECTED) {
            setRssiDirect(0, RSSI_SOURCE_RX_PROTOCOL);
#ifdef USE_RX_RSSI_DBM
            setRssiDbmDirect(-130, RSSI_SOURCE_RX_PROTOCOL);
#endif
#ifdef USE_RX_LINK_QUALITY_INFO
            setLinkQualityDirect(0);
#endif
        } else {
            receiver.rssiFiltered = simpleLPFilterUpdate(&rssiFilter, receiver.rssi);
            uint16_t rssiScaled = scaleRange(constrain(receiver.rssiFiltered, receiver.rf_perf_params->sensitivity, -50), receiver.rf_perf_params->sensitivity, -50, 0, 1023);
            setRssi(rssiScaled, RSSI_SOURCE_RX_PROTOCOL);
#ifdef USE_RX_RSSI_DBM
            setRssiDbm(receiver.rssiFiltered, RSSI_SOURCE_RX_PROTOCOL);
#endif
#ifdef USE_RX_LINK_QUALITY_INFO
            setLinkQualityDirect(receiver.uplinkLQ);
            rxSetRfMode((uint8_t)RATE_4HZ - (uint8_t)receiver.mod_params->enumRate);
#endif
#ifdef USE_RX_LINK_UPLINK_POWER
            rxSetUplinkTxPwrMw(txPowerIndexToValue(txPower));
#endif
        }
    }
}

static void handleTelemetryUpdate(void)
{
    if (receiver.connectionState != CONNECTED || (receiver.mod_params->tlmInterval == TLM_RATIO_NO_TLM)) {
        return;
    }

    uint8_t *nextPayload = 0;
    uint8_t nextPlayloadSize = 0;
    if (!isTelemetrySenderActive() && getNextTelemetryPayload(&nextPlayloadSize, &nextPayload)) {
        setTelemetryDataToTransmit(nextPlayloadSize, nextPayload, ELRS_TELEMETRY_BYTES_PER_CALL);
    }
    updateTelemetryBurst();
}

void expressLrsSetRcDataFromPayload(uint16_t *rcData, const uint8_t *payload)
{
    if (rcData && payload) {
        rxExpressLrsSpiConfig()->switchMode == SM_HYBRID_WIDE ? unpackChannelDataHybridWide(rcData, payload) : unpackChannelDataHybridSwitch8(rcData, payload);
    }
}

static void enterBindingMode(void)
{
    if ((receiver.connectionState == CONNECTED) || receiver.inBindingMode) {
        // Don't enter binding if:
        // - we're already connected
        // - we're already binding
        return;
    }

    // Set UID to special binding values
    receiver.UID = BindingUID;
    crcInitializer = 0;
    receiver.inBindingMode = true;
    
    setRFLinkRate(bindingRateIndex);
    startReceiving();
}

rx_spi_received_e expressLrsDataReceived(uint8_t *payload)
{
    rx_spi_received_e result = RX_SPI_RECEIVED_NONE;
    uint32_t isrTimeStampUs;

    if (rxSpiCheckBindRequested(true)) {
        enterBindingMode();
    }

    uint8_t irqReason = receiver.rxISR(&isrTimeStampUs);
    if (irqReason == DIO_TX_DONE) {
        startReceiving();
    } else if (irqReason == DIO_RX_DONE) {
        result = processRFPacket(payload);
    }

    if (receiver.fhssRequired) {
        receiver.fhssRequired = false;
        bool didFHSS = handleFHSS();
        bool tlmSent = handleSendTelemetryResponse();

        if (!didFHSS && !tlmSent && lqPeriodIsSet()) {
            receiver.handleFreqCorrection(receiver.freqOffset, receiver.currentFreq); //corrects for RX freq offset
        }
    }

    DEBUG_SET(DEBUG_RX_EXPRESSLRS_SPI, 0, receiver.inBindingMode);
    DEBUG_SET(DEBUG_RX_EXPRESSLRS_SPI, 1, receiver.rssiFiltered);
    DEBUG_SET(DEBUG_RX_EXPRESSLRS_SPI, 2, receiver.snr);
    DEBUG_SET(DEBUG_RX_EXPRESSLRS_SPI, 3, receiver.uplinkLQ);

    const uint32_t timeStampMs = millis();

    handleConnectionStateUpdate(timeStampMs);
    handleConfigUpdate(timeStampMs);
    handleLinkStatsUpdate(timeStampMs);
    handleTelemetryUpdate();

    receiver.inBindingMode ? rxSpiLedBlinkBind() : rxSpiLedBlinkRxLoss(result);

    return result;
}

#endif /* USE_RX_EXPRESSLRS */
