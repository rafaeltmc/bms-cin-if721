(new System()).init('#system-switch','#system-state', '#power-solar', '#power-battery');
(new CarControls()).init('#car-start-stop', '#car-pedal-accelerator', '#car-pedal-break');
(new Sky()).init('#sky');
(new Sensor('BATTERY_PACK', 'VOLTAGE')).init();
