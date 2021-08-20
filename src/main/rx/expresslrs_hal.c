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
 * Dominic Clifton/Hydra - Timer-based timeout implementation.
 */

#include <string.h>
#include "platform.h"

#ifdef USE_RX_EXPRESSLRS

#include "build/debug_pin.h"

#include "drivers/timer.h"

#include "drivers/nvic.h"

#include "rx/expresslrs_common.h"
#include "rx/expresslrs_impl.h"

#include "common/maths.h"

#define TIMER_INTERVAL_US_DEFAULT 20000
#define TICK_TOCK_COUNT 2

typedef enum {
    TICK,
    TOCK
} tickTock_e;

typedef struct elrsTimerState_s {
    volatile tickTock_e tickTock;
    uint32_t intervalUs;
    int32_t frequencyOffsetTicks;

    int32_t phaseShift;

} elrsTimerState_t;

// Use a little ram to keep the amount of CPU cycles used in the ISR lower.
typedef struct elrsPhaseShiftLimits_s {
    int32_t min;
    int32_t max;
} elrsPhaseShiftLimits_t;

elrsPhaseShiftLimits_t phaseShiftLimits;

static elrsTimerState_t timerState = {
    TOCK, // Start on TOCK (in ELRS isTick is initialised to false)
    TIMER_INTERVAL_US_DEFAULT,
    0,
    0
};

static void expressLrsRecalculatePhaseShiftLimits(void)
{
    phaseShiftLimits.max = (timerState.intervalUs / TICK_TOCK_COUNT);
    phaseShiftLimits.min = -phaseShiftLimits.max;
}

uint16_t expressLrsCalculateMaximumExpectedPeriod(uint16_t intervalUs)
{
    // The timer reload register must not overflow when frequencyOffsetTicks is added to it.
    // frequencyOffsetTicks is not expected to be higher than 1/4 of the interval.
    // also, timer resolution must be as high as possible.
    const uint16_t maximumExpectedPeriod = (intervalUs / TICK_TOCK_COUNT) + (timerState.intervalUs / 4);
    return maximumExpectedPeriod;
}

void expressLrsUpdateTimerInterval(TIM_TypeDef *timer, uint16_t intervalUs)
{
    timerState.intervalUs = intervalUs;
    expressLrsRecalculatePhaseShiftLimits();

    timerReconfigureTimeBase(timer, expressLrsCalculateMaximumExpectedPeriod(timerState.intervalUs), MHZ_TO_HZ(1));

    LL_TIM_SetAutoReload(timer, ((intervalUs / TICK_TOCK_COUNT) - 1) & 0xffff);
}

void expressLrsUpdatePhaseShift(int32_t newPhaseShift)
{
    timerState.phaseShift = constrain(newPhaseShift, phaseShiftLimits.min, phaseShiftLimits.max);
}

static void expressLrsOnTimerUpdate(timerOvrHandlerRec_t *cbRec, captureCompare_t capture)
{
    UNUSED(cbRec);
    UNUSED(capture);

    elrsReceiver_t *self = container_of(cbRec, elrsReceiver_t, timerUpdateCb);

    if (timerState.tickTock == TICK) {
        DEBUG_HI(0);

        expressLrsOnTimerTickISR();

        timerState.tickTock = TOCK;
    } else {
        DEBUG_LO(0);

        expressLrsOnTimerTockISR();

        timerState.tickTock = TICK;
    }


    UNUSED(self);
}


void expressLrsInitialiseTimer(elrsReceiver_t *receiver)
{
    receiver->timer = RX_EXPRESSLRS_TIMER_INSTANCE;


    configTimeBase(receiver->timer, expressLrsCalculateMaximumExpectedPeriod(timerState.intervalUs), MHZ_TO_HZ(1));

    expressLrsUpdateTimerInterval(receiver->timer, timerState.intervalUs);

    timerChOvrHandlerInit(&receiver->timerUpdateCb, expressLrsOnTimerUpdate);

    timerConfigUpdateCallback(receiver->timer, &receiver->timerUpdateCb);

    uint8_t irq = timerInputIrq(receiver->timer);

    // Use the NVIC TIMER priority for now
    HAL_NVIC_SetPriority(irq, NVIC_PRIORITY_BASE(NVIC_PRIO_TIMER), NVIC_PRIORITY_SUB(NVIC_PRIO_TIMER));
    HAL_NVIC_EnableIRQ(irq);

    LL_TIM_EnableCounter(receiver->timer);
}

#endif
