#ifndef GPIO_LINUX_H_
#define GPIO_LINUX_H_

// Set the value of GPIO output `index` to `value`.  This will open the GPIO
// device the first time it's called.
void gpio_set_value(int index, int value);

#endif // GPIO_LINUX_H_
