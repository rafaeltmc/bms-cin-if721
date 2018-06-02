/* BMS
 */
MACHINE
    BMS
DEFINITIONS 
    "INPUTS.def";
    "SENSORS_RANGE.def"
SETS
    SYS_STATES = {
        OFF,
        START,
        NORMAL,
        ISSUE, 
        CRITICAL
    };

    INPUTS_TYPE = {
        SOLAR_CELL_ARRAY_VOLTAGE,
        SOLAR_CELL_ARRAY_CURRENT,
        BATTERY_PACK_VOLTAGE,
        BATTERY_PACK_CURRENT,
        BATTERY_PACK_TEMPERATURE,
        SINGLE_BATTERY_VOLTAGE,
        SINGLE_BATTERY_CURRENT,
        LOAD_CURRENT_DRAIN
    }
PROPERTIES
    INPUTS : NATURAL +->> INPUTS_TYPE
    & ! param . (param : {
            VOLTAGE_MIN,
	        VOLTAGE_MAX,
        	CURRENT_MIN,
        	CURRENT_MAX,
        	TEMPERATURE_MIN,
        	TEMPERATURE_MAX} => param : NATURAL)
VARIABLES
    sys_state,
    sys_start_missing_inputs,
    
    inputs_last_value    
INVARIANT
    sys_state : SYS_STATES
    & sys_start_missing_inputs <: dom(INPUTS)
    
    & inputs_last_value : dom(INPUTS) +-> NATURAL
    
    & sys_start_missing_inputs /\ dom(inputs_last_value) = {}
    
    // Garantee that sensor values does not exceed its range
    & ! (sensor_id, sensor_value) 
        . (sensor_id |-> sensor_value : inputs_last_value 
            => ((INPUTS(sensor_id) : {SOLAR_CELL_ARRAY_VOLTAGE, 
                                     BATTERY_PACK_VOLTAGE, 
                                     SINGLE_BATTERY_VOLTAGE} 
                    => (sensor_value >= VOLTAGE_MIN & sensor_value <= VOLTAGE_MAX))
                & (INPUTS(sensor_id) : {SOLAR_CELL_ARRAY_CURRENT, 
                                        BATTERY_PACK_CURRENT, 
                                        SINGLE_BATTERY_CURRENT, 
                                        LOAD_CURRENT_DRAIN} 
                    => (sensor_value >= CURRENT_MIN & sensor_value <= CURRENT_MAX))
                & (INPUTS(sensor_id) : {BATTERY_PACK_TEMPERATURE} 
                    => (sensor_value >= TEMPERATURE_MIN & sensor_value <= TEMPERATURE_MAX))))
INITIALISATION
    sys_state := OFF
    || sys_start_missing_inputs := {}
    
    || inputs_last_value := {}
OPERATIONS
    /*
     * Turn the system ON
     *
     * Pre: The system must be OFF
     * 
     * Put the system in START state and reset the missing input list and old input values
     */
    turnOn =
    PRE
        sys_state = OFF
    THEN
        sys_state := START
        || sys_start_missing_inputs := dom(INPUTS)
        || inputs_last_value := {}
    END;
    
    /*
     * Turn the system OFF
     *
     * Pre: The system must not be already OFF
     * 
     * Put the system in OFF state
     */
    turnOff =
    PRE
        sys_state /= OFF
    THEN
        sys_state := OFF
    END;
    
    /*
     * Set first input readings
     *
     * Pre: The system must be in START state
     *      The id must be valid and not have an initial value
     * 
     * Updates a voltage input value based on sensor id
     */
    setSensorValue(sensor_id, value) =
    PRE
        sys_state = START
        & sensor_id : dom(INPUTS)
        & sensor_id : sys_start_missing_inputs
        & value : NATURAL
        & (INPUTS(sensor_id) : {SOLAR_CELL_ARRAY_VOLTAGE, 
                                BATTERY_PACK_VOLTAGE, 
                                SINGLE_BATTERY_VOLTAGE}  => (value >= VOLTAGE_MIN & value <= VOLTAGE_MAX))
        & (INPUTS(sensor_id) : {SOLAR_CELL_ARRAY_CURRENT, 
                                BATTERY_PACK_CURRENT, 
                                SINGLE_BATTERY_CURRENT, 
                                LOAD_CURRENT_DRAIN}  => (value >= CURRENT_MIN & value <= CURRENT_MAX & value mod 100 = 0))
        & (INPUTS(sensor_id) : {BATTERY_PACK_TEMPERATURE}  => (value >= TEMPERATURE_MIN & value <= TEMPERATURE_MAX))
    THEN
        inputs_last_value := inputs_last_value \/ {sensor_id |-> value}
        || sys_start_missing_inputs := sys_start_missing_inputs - {sensor_id}
        || 
        IF card(sys_start_missing_inputs) = 1 THEN
            sys_state := NORMAL
        END
    END;
    
    /*
     * Update voltage input value for a Solar Cell Array
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The voltage value must be a natural within the voltage range
     *      The difference between the previous and updated values must not be greater than 1V
     * 
     * Updates a voltage input value based on sensor id
     */
    updateSolarCellArrayVoltage(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = SOLAR_CELL_ARRAY_VOLTAGE
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= VOLTAGE_MIN
        & value <= VOLTAGE_MAX
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 1)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 1)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update current input value for a Solar Cell Array
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated values must not be greater than 100mA
     * 
     * Updates a current input value based on sensor id
     */
    updateSolarCellArrayCurrent(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = SOLAR_CELL_ARRAY_CURRENT
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= CURRENT_MIN
        & value <= CURRENT_MAX
        & value mod 100 = 0
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 100)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 100)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update voltage input value for a Battery Pack
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The voltage value must be a natural within the voltage range
     *      The difference between the previous and updated values must not be greater than 1V
     * 
     * Updates a voltage input value based on sensor id
     */
    updateBatteryPackVoltage(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = BATTERY_PACK_VOLTAGE
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= VOLTAGE_MIN
        & value <= VOLTAGE_MAX
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 1)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 1)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update current input value for a Battery Pack
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated values must not be greater than 100mA
     * 
     * Updates a current input value based on sensor id
     */
    updateBatteryPackCurrent(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = BATTERY_PACK_CURRENT
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= CURRENT_MIN
        & value <= CURRENT_MAX
        & value mod 100 = 0
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 100)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 100)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update temperature input value for a Battery Pack
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The temperature value must be a natural within the temperaeture range
     *      The difference between the previous and updated values must not be greater than 1ºC
     * 
     * Updates a temperature input value based on sensor id
     */
    updateBatteryPackTemperature(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = BATTERY_PACK_TEMPERATURE
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= TEMPERATURE_MIN
        & value <= TEMPERATURE_MAX
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 1)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 1)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update voltage input value for a Single Battery
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The voltage value must be a natural within the voltage range
     *      The difference between the previous and updated values must not be greater than 1V
     * 
     * Updates a voltage input value based on sensor id
     */
    updateSingleBatteryVoltage(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = SINGLE_BATTERY_VOLTAGE
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= VOLTAGE_MIN
        & value <= VOLTAGE_MAX
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 1)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 1)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update current input value for a Single Battery
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated values must not be greater than 100mA
     * 
     * Updates a current input value based on sensor id
     */
    updateSingleBatteryCurrent(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = SINGLE_BATTERY_CURRENT
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= CURRENT_MIN
        & value <= CURRENT_MAX
        & value mod 100 = 0
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 100)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 100)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END;
    
    /*
     * Update current drain input value for a Load
     *
     * Pre: The system must not be OFF nor in START state
     *      The sensor id must be valid 
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated values must not be greater than 100mA
     * 
     * Updates a current input value based on sensor id
     */
    updateLoadCurrentDrain(sensor_id, value) =
    PRE
        sys_state /: {OFF, START}
        & sensor_id : dom(INPUTS)
        & INPUTS(sensor_id) = LOAD_CURRENT_DRAIN
        & value : NATURAL
        & value /= inputs_last_value(sensor_id)
        & value >= CURRENT_MIN
        & value <= CURRENT_MAX
        & value mod 100 = 0
        & (inputs_last_value(sensor_id) > value => inputs_last_value(sensor_id)-value = 100)
        & (inputs_last_value(sensor_id) < value => value-inputs_last_value(sensor_id) = 100)
    THEN
        inputs_last_value := inputs_last_value <+ {sensor_id |-> value}
    END
    
END
