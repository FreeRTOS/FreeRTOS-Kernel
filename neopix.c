#include<stdio.h>
#include "pico/stdlib.h"

#include "FreeRTOS.h"

#include "task.h"

void vBlinkTask()
{

    vTaskDelay(1000);
    for (;;)
    {
        gpio_put(PICO_DEFAULT_LED_PIN, 1);
        vTaskDelay(250);
        gpio_put(PICO_DEFAULT_LED_PIN, 0);
        vTaskDelay(250);
        sleep_ms(10);
    }
}

void main()
{
    stdio_init_all();
    gpio_init(PICO_DEFAULT_LED_PIN);

    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);

    xTaskCreate(vBlinkTask, "Blink Task", 128, NULL, 1, NULL);

    vTaskStartScheduler();
}
