/* BMS
 */
MACHINE
    BMS
DEFINITIONS 
    "UNIT_PARAMS.def";
    "SENSORS_RANGE.def"
SETS
    SYS_STATES = {
        OFF,
        START,
        NORMAL,
        ISSUE, 
        CRITICAL
    };

    UNIT = {
        SOLAR_CELL_ARRAY,
        BATTERY_PACK,
        SINGLE_BATTERY_1,
        SINGLE_BATTERY_2,
        LOAD
    };

    SENSOR_TYPE = {
        VOLTAGE,
        CURRENT,
        TEMPERATURE
    };

    UNIT_STATES = {
        UNIT_NORMAL,
        UNIT_ISSUE,
        UNIT_CRITICAL
    };
    
    SWITCH_STATE = {
        SWITCH_ON,
        SWITCH_OFF
    };
    
    FAN_SPEED = {
       FAN_STOP,
       FAN_LOW,
       FAN_MID,
       FAN_HIGH
    }
CONSTANTS
	UNIT_ISSUE_LOWER_THRESHOLD,
	UNIT_CRITICAL_LOWER_THRESHOLD
PROPERTIES
    ! param . (param : {
            VOLTAGE_MIN,
	        VOLTAGE_MAX,
        	CURRENT_MIN,
        	CURRENT_MAX,
        	TEMPERATURE_MIN,
        	TEMPERATURE_MAX} => param : NATURAL)
 
    & UNIT_ISSUE_LOWER_THRESHOLD = {
		(SOLAR_CELL_ARRAY, (VOLTAGE, 3)),
        (SOLAR_CELL_ARRAY, (CURRENT, 300)),
        (BATTERY_PACK, (VOLTAGE, 3)),
        (BATTERY_PACK, (CURRENT, 300)),
        (BATTERY_PACK, (TEMPERATURE, 30)),
        (SINGLE_BATTERY_1, (VOLTAGE, 2)),
        (SINGLE_BATTERY_1, (CURRENT, 200)),
        (SINGLE_BATTERY_2, (VOLTAGE, 2)),
        (SINGLE_BATTERY_2, (CURRENT, 300)),
        (LOAD, (CURRENT, 300))
	}
    	
	& UNIT_CRITICAL_LOWER_THRESHOLD = {
		(SOLAR_CELL_ARRAY, (VOLTAGE, 4)),
        (SOLAR_CELL_ARRAY, (CURRENT, 400)),
        (BATTERY_PACK, (VOLTAGE, 4)),
        (BATTERY_PACK, (CURRENT, 400)),
        (BATTERY_PACK, (TEMPERATURE, 40)),
        (SINGLE_BATTERY_1, (VOLTAGE, 3)),
        (SINGLE_BATTERY_1, (CURRENT, 300)),
        (SINGLE_BATTERY_2, (VOLTAGE, 3)),
        (SINGLE_BATTERY_2, (CURRENT, 300)),
        (LOAD, (CURRENT, 400))
	}
VARIABLES
    sys_state,
    sys_start_missing_inputs,
    
    inputs_last_value,
    units_state,
    
    power_mux,
    
    load_user_switch,
    load_kill_switch,
    load_switch,
    battery_switch,
    
    fan_speed,
    
    battery_unbalanced,
    
    charging_attempts_counts
INVARIANT
    sys_state : SYS_STATES
    & sys_start_missing_inputs <: UNIT
    
    & inputs_last_value : UNIT +-> (SENSOR_TYPE +-> NATURAL)
    & units_state : UNIT --> UNIT_STATES
    
    & sys_start_missing_inputs /\ dom(inputs_last_value) = {}
    
    // Garantee that sensor values does not exceed its range
    & ! (unit_type, sensor_type, sensor_value, TEMP) 
        . ((unit_type |-> TEMP : inputs_last_value & sensor_type |->  sensor_value : TEMP)
            => (sensor_type = VOLTAGE => (sensor_value >= VOLTAGE_MIN & sensor_value <= VOLTAGE_MAX))
                & (sensor_type = CURRENT => (sensor_value >= CURRENT_MIN & sensor_value <= CURRENT_MAX))
                & (sensor_type = TEMPERATURE => (sensor_value >= TEMPERATURE_MIN & sensor_value <= TEMPERATURE_MAX)))
            
    // Power Mutex must interligate 2 main units
    & power_mux : POW({SOLAR_CELL_ARRAY, BATTERY_PACK, LOAD})
    & card(power_mux) = 2
    
    & load_switch : SWITCH_STATE
    & load_kill_switch : SWITCH_STATE
    & load_user_switch : SWITCH_STATE
    & battery_switch : SWITCH_STATE
    
    // Garantee the load is not killed when it is NOT on CRITICAL state
    & (sys_state /= CRITICAL => load_kill_switch = SWITCH_OFF)
    
    // Garantee the load is off when on CRITICAL state
    & (sys_state = CRITICAL => load_kill_switch = SWITCH_ON)
    
    // Garantee the battery is being recharged when CRITICAL
    & ((units_state[{BATTERY_PACK}] /\ {UNIT_CRITICAL} /= {}) => battery_switch = SWITCH_OFF)
    
    // Garantee the load is off when reach CRITICAL
    & ((units_state[{LOAD}] /\ {UNIT_CRITICAL} /= {}) => load_kill_switch = SWITCH_ON)
    
    // Garantee the solar cell is not being used when CRITICAL
    & ((units_state[{SOLAR_CELL_ARRAY}] /\ {UNIT_CRITICAL} /= {}) => (SOLAR_CELL_ARRAY : power_mux => (battery_switch = SWITCH_OFF & load_switch = SWITCH_OFF)))
    
    & fan_speed : FAN_SPEED
    & battery_unbalanced : BOOL
    & charging_attempts_counts : NATURAL
INITIALISATION
    sys_state := OFF
    || sys_start_missing_inputs := UNIT
    
    || inputs_last_value := {}
    || units_state := UNIT * {UNIT_NORMAL}
    
    || power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
    
    || load_switch := SWITCH_OFF
    || load_kill_switch := SWITCH_OFF
    || load_user_switch := SWITCH_OFF
    || battery_switch := SWITCH_OFF
    
    || fan_speed := FAN_STOP
    || battery_unbalanced := FALSE
	|| charging_attempts_counts := 0
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
        || sys_start_missing_inputs := UNIT
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
                    
        || units_state := UNIT * {UNIT_NORMAL}
        || sys_start_missing_inputs := UNIT
        || inputs_last_value := {}
        || power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
        || load_switch := SWITCH_OFF
        || load_kill_switch := SWITCH_OFF
        || load_user_switch := SWITCH_OFF
        || battery_switch := SWITCH_OFF
        || fan_speed := FAN_STOP
        || battery_unbalanced := FALSE
        || charging_attempts_counts := 0
    END;
    
    /*
     * Set first input readings
     *
     * Pre: The system must be in START state
     *      An initial value must not exist
     * 
     * Initializes a voltage and current input value of a solar cell array
     */
    initializeSolarCellArray(unit, voltage, current) =
    PRE
        sys_state = START
        & unit = SOLAR_CELL_ARRAY
        & unit : sys_start_missing_inputs
        & voltage : NATURAL
        & voltage >= VOLTAGE_MIN 
        & voltage <= VOLTAGE_MAX
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
    THEN
        inputs_last_value := inputs_last_value \/ {unit |-> {VOLTAGE |-> voltage, CURRENT |-> current}}
        || sys_start_missing_inputs := sys_start_missing_inputs - {unit}
        ||
        IF card(sys_start_missing_inputs) = 1 THEN
            sys_state := NORMAL
                    
            || power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            || load_kill_switch := SWITCH_OFF
            || load_user_switch := SWITCH_OFF
            || battery_switch := SWITCH_OFF
            || fan_speed := FAN_STOP
            || battery_unbalanced := FALSE
            || charging_attempts_counts := 0
        END
    END;
    
    /*
     * Set first input readings
     *
     * Pre: The system must be in START state
     *      An initial value must not exist
     * 
     * Initializes a voltage, current and temperature input value of a battery pack
     */
    initializeBatteryPack(unit, voltage, current, temperature) =
    PRE
        sys_state = START
        & unit = BATTERY_PACK
        & unit : sys_start_missing_inputs
        & voltage : NATURAL
        & voltage >= VOLTAGE_MIN 
        & voltage <= VOLTAGE_MAX
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
        & temperature : NATURAL
        & temperature >= TEMPERATURE_MIN 
        & temperature <= TEMPERATURE_MAX
    THEN
        inputs_last_value := inputs_last_value \/ {unit |-> {VOLTAGE |-> voltage, CURRENT |-> current, TEMPERATURE |-> temperature}}
        || sys_start_missing_inputs := sys_start_missing_inputs - {unit}
        ||
        IF card(sys_start_missing_inputs) = 1 THEN
            sys_state := NORMAL
                    
            || power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            || load_kill_switch := SWITCH_OFF
            || load_user_switch := SWITCH_OFF
            || battery_switch := SWITCH_OFF
            || fan_speed := FAN_STOP
            || battery_unbalanced := FALSE
            || charging_attempts_counts := 0
        END
    END;
    
    /*
     * Set first input readings
     *
     * Pre: The system must be in START state
     *      An initial value must not exist
     * 
     * Initializes a voltage, current input value of a single battery
     */
    initializeSingleBattery(unit, voltage, current) =
    PRE
        sys_state = START
        & unit : {SINGLE_BATTERY_1, SINGLE_BATTERY_2}
        & unit : sys_start_missing_inputs
        & voltage : NATURAL
        & voltage >= VOLTAGE_MIN 
        & voltage <= VOLTAGE_MAX
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
    THEN
        inputs_last_value := inputs_last_value \/ {unit |-> {VOLTAGE |-> voltage, CURRENT |-> current}}
        || sys_start_missing_inputs := sys_start_missing_inputs - {unit}
        ||
        IF card(sys_start_missing_inputs) = 1 THEN
            sys_state := NORMAL
                    
            || power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            || load_kill_switch := SWITCH_OFF
            || load_user_switch := SWITCH_OFF
            || battery_switch := SWITCH_OFF
            || fan_speed := FAN_STOP
            || battery_unbalanced := FALSE
            || charging_attempts_counts := 0
        END
    END;
    
    /*
     * Set first input readings
     *
     * Pre: The system must be in START state
     *      An initial value must not exist
     * 
     * Initializes a current input value of the load
     */
    initializeLoad(unit, current) =
    PRE
        sys_state = START
        & unit = LOAD
        & unit : sys_start_missing_inputs
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
        & (load_user_switch = SWITCH_OFF => current = 0)
    THEN
        inputs_last_value := inputs_last_value \/ {unit |-> {CURRENT |-> current}}
        || sys_start_missing_inputs := sys_start_missing_inputs - {unit}
        ||
        IF card(sys_start_missing_inputs) = 1 THEN
            sys_state := NORMAL
                    
            || power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            || load_kill_switch := SWITCH_OFF
            || load_user_switch := SWITCH_OFF
            || battery_switch := SWITCH_OFF
            || fan_speed := FAN_STOP
            || battery_unbalanced := FALSE
            || charging_attempts_counts := 0
        END
    END;
    
    /*
     * Update input values for a Solar Cell Array
     *
     * Pre: The system must not be OFF nor in START state
     *      The unit must be a solar cell array
     *      The voltage value must be a natural within the voltage range
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated voltage values must not be greater than 1V
     *      The difference between the previous and updated current values must not be greater than 100mA
     * 
     * Updates input values based for a unit
     */
    updateSolarCellArray(unit, voltage, current) =
    PRE
        sys_state /: {OFF, START}
        & unit = SOLAR_CELL_ARRAY
        & voltage : NATURAL
        & voltage >= VOLTAGE_MIN 
        & voltage <= VOLTAGE_MAX
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
        & (inputs_last_value(unit)(VOLTAGE) > voltage => inputs_last_value(unit)(VOLTAGE)-voltage <= 1)
        & (inputs_last_value(unit)(VOLTAGE) <= voltage => voltage-inputs_last_value(unit)(VOLTAGE) <= 1)
        & (inputs_last_value(unit)(CURRENT) > current => inputs_last_value(unit)(CURRENT)-current <= 100)
        & (inputs_last_value(unit)(CURRENT) <= current => current-inputs_last_value(unit)(CURRENT) <= 100)
        & inputs_last_value(unit) /= {VOLTAGE |-> voltage, CURRENT |-> current}
    THEN
        // Updates unit sensor values
        inputs_last_value := inputs_last_value <+ {unit |-> {VOLTAGE |-> voltage, CURRENT |-> current}}
        ||
        // Updates unit current state
        IF voltage >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE)
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
        THEN
            units_state := units_state <+ {unit |-> UNIT_CRITICAL}
        ELSIF voltage >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            units_state := units_state <+ {unit |-> UNIT_ISSUE}
        ELSE
            units_state := units_state <+ {unit |-> UNIT_NORMAL}
        END
        ||
        // Updates system state based on current conditions
        IF UNIT_CRITICAL : units_state[UNIT - {unit}]
            or voltage >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            // Critical state
            sys_state := CRITICAL
            || load_kill_switch := SWITCH_ON
        ELSIF UNIT_ISSUE : units_state[UNIT - {unit}]
            or voltage >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            // Issue state
            sys_state := ISSUE
            || load_kill_switch := SWITCH_OFF
        ELSE
            // Normal operation
            sys_state := NORMAL
            || load_kill_switch := SWITCH_OFF
        END
        ||
        // Updates system operation
        IF load_user_switch = SWITCH_ON
            & load_kill_switch = SWITCH_OFF
            
            & voltage < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            & current < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT) 
            
            & voltage >= LOAD_VOLTAGE
            
            & units_state(LOAD) /= UNIT_CRITICAL
        THEN
            // Supply power when:
            //     - Load is ON and is NOT Killed by critical condition
            //     - Solar Cell Array is not on CRITICAL conditions
            //     - Solar Cell Array voltage is enough for the load
            //     - Load is not on critical condition
            power_mux := {SOLAR_CELL_ARRAY, LOAD}
            || battery_switch := SWITCH_OFF
            || load_switch := SWITCH_ON
        ELSIF (load_user_switch = SWITCH_OFF or load_kill_switch = SWITCH_ON)
            
            & voltage < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            & current < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
            
            & inputs_last_value(BATTERY_PACK)(VOLTAGE) < UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            
            & voltage > inputs_last_value(BATTERY_PACK)(VOLTAGE)
            & units_state(BATTERY_PACK) /= UNIT_CRITICAL
        THEN
            // Recharge battery when:
            //     - Load is OFF or is Killed by critical condition
            //     - Solar Cell Array is not on CRITICAL conditions
            //     - Battery voltage is lower than battery ISSUE threshold
            //     - Solar Cell Array voltage is higher than battery voltage
            //     - Battery pack is not on critical condition
            power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            ||
            IF battery_switch = SWITCH_OFF
			THEN
				battery_switch := SWITCH_ON
				|| charging_attempts_counts := max({5, charging_attempts_counts + 1})
			END
        ELSIF load_user_switch = SWITCH_ON 
            & load_kill_switch = SWITCH_OFF
            & inputs_last_value(BATTERY_PACK)(VOLTAGE) >= LOAD_VOLTAGE
            & units_state(BATTERY_PACK) /= UNIT_CRITICAL
        THEN
            // Switch to battery supply:
            //     - Load is ON and NOT Killed by critical condition
            //     - Load current is not at the critical threshold
            //     - Battery Pack voltage is enough
            //     - Battery Pack is not on critical condition
            power_mux := {BATTERY_PACK, LOAD}
            || load_switch := SWITCH_ON
            || battery_switch := SWITCH_ON
        ELSIF SOLAR_CELL_ARRAY : power_mux
        THEN
        // If no operations are avaiable for the solar cell array, but it is selected on the mux, turn the switches off
            battery_switch := SWITCH_OFF
            || load_switch := SWITCH_OFF
        END
    END;
    
    /*
     * Update input values for a Single Battery Pack
     *
     * Pre: The system must not be OFF nor in START state
     *      The unit must be a single battery
     *      The voltage value must be a natural within the voltage range
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated voltage values must not be greater than 1V
     *      The difference between the previous and updated current values must not be greater than 100mA
     * 
     * Updates input values based for a unit
     */
    updateSingleBattery(unit, voltage, current) =
    PRE
        sys_state /: {OFF, START}
        & unit : {SINGLE_BATTERY_1, SINGLE_BATTERY_2}
        & voltage : NATURAL
        & voltage >= VOLTAGE_MIN 
        & voltage <= VOLTAGE_MAX
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
        & (inputs_last_value(unit)(VOLTAGE) > voltage => inputs_last_value(unit)(VOLTAGE)-voltage <= 1)
        & (inputs_last_value(unit)(VOLTAGE) <= voltage => voltage-inputs_last_value(unit)(VOLTAGE) <= 1)
        & (inputs_last_value(unit)(CURRENT) > current => inputs_last_value(unit)(CURRENT)-current <= 100)
        & (inputs_last_value(unit)(CURRENT) <= current => current-inputs_last_value(unit)(CURRENT) <= 100)
        & inputs_last_value(unit) /= {VOLTAGE |-> voltage, CURRENT |-> current}
    THEN
        // Updates unit sensor values
        inputs_last_value := inputs_last_value <+ {unit |-> {VOLTAGE |-> voltage, CURRENT |-> current}}
        ||
        // Updates unit current state
        IF voltage >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE)
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
        THEN
            units_state := units_state <+ {unit |-> UNIT_CRITICAL}
        ELSIF voltage >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            units_state := units_state <+ {unit |-> UNIT_ISSUE}
        ELSE
            units_state := units_state <+ {unit |-> UNIT_NORMAL}
        END
        ||
        // Updates system state based on current conditions
        IF UNIT_CRITICAL : units_state[UNIT - {unit}]
            or voltage >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
        THEN
            // Critical state
            sys_state := CRITICAL
            || load_kill_switch := SWITCH_ON
        ELSIF UNIT_ISSUE : units_state[UNIT - {unit}]
            or voltage >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            // Issue state
            sys_state := ISSUE
            || load_kill_switch := SWITCH_OFF
        ELSE
            // Normal operation
            sys_state := NORMAL
            || load_kill_switch := SWITCH_OFF
        END
        ||
        IF (# battery . 
                (battery : inputs_last_value[{SINGLE_BATTERY_1, SINGLE_BATTERY_2} - {unit}]
                    & ((voltage > battery(VOLTAGE) => voltage - battery(VOLTAGE) >= 1)
                        & (battery(VOLTAGE) >= voltage => battery(VOLTAGE) - voltage >= 1))))
        THEN
            battery_unbalanced := TRUE
        ELSE
            battery_unbalanced := FALSE
        END
    END;
    
    /*
     * Update input values for a Battery Pack
     *
     * Pre: The system must not be OFF nor in START state
     *      The unit must be a battery pack
     *      The voltage value must be a natural within the voltage range
     *      The current value must be a natural within the current range
     *      The temperature value must be a natural within the temprature range
     *      The difference between the previous and updated voltage values must not be greater than 1V
     *      The difference between the previous and updated current values must not be greater than 100mA
     *      The difference between the previous and updated temperature values must not be greater than 10ºC
     * 
     * Updates input values based for a unit
     */
    updateBatteryPack(unit, voltage, current, temperature) =
    PRE
        sys_state /: {OFF, START}
        & unit = BATTERY_PACK
        & voltage : NATURAL
        & voltage >= VOLTAGE_MIN 
        & voltage <= VOLTAGE_MAX
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
        & temperature : NATURAL
        & temperature >= TEMPERATURE_MIN 
        & temperature <= TEMPERATURE_MAX 
        & temperature mod 10 = 0
        & (inputs_last_value(unit)(VOLTAGE) > voltage => inputs_last_value(unit)(VOLTAGE)-voltage <= 1)
        & (inputs_last_value(unit)(VOLTAGE) <= voltage => voltage-inputs_last_value(unit)(VOLTAGE) <= 1)
        & (inputs_last_value(unit)(CURRENT) > current => inputs_last_value(unit)(CURRENT)-current <= 100)
        & (inputs_last_value(unit)(CURRENT) <= current => current-inputs_last_value(unit)(CURRENT) <= 100)
        & (inputs_last_value(unit)(TEMPERATURE) > temperature => inputs_last_value(unit)(TEMPERATURE)-temperature <= 10)
        & (inputs_last_value(unit)(TEMPERATURE) <= temperature => temperature-inputs_last_value(unit)(TEMPERATURE) <= 10)
        & inputs_last_value(unit) /= {VOLTAGE |-> voltage, CURRENT |-> current, TEMPERATURE |-> temperature}
    THEN
        // Updates unit sensor values
        inputs_last_value := inputs_last_value <+ {unit |-> {VOLTAGE |-> voltage, CURRENT |-> current, TEMPERATURE |-> temperature}}
        ||
        // Updates unit current state
        IF voltage >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE)
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
            or temperature >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](TEMPERATURE)
        THEN
            units_state := units_state <+ {unit |-> UNIT_CRITICAL}
        ELSIF voltage >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
            or temperature >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            units_state := units_state <+ {unit |-> UNIT_ISSUE}
        ELSE
            units_state := units_state <+ {unit |-> UNIT_NORMAL}
        END
        ||
        // Updates system state based on current conditions
        IF UNIT_CRITICAL : units_state[UNIT - {unit}]
            or voltage >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT) 
            or temperature >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            // Critical state
            sys_state := CRITICAL
            || load_kill_switch := SWITCH_ON
        ELSIF UNIT_ISSUE : units_state[UNIT - {unit}]
            or voltage >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
            or temperature >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            // Issue state
            sys_state := ISSUE
            || load_kill_switch := SWITCH_OFF
        ELSE
            // Normal operation
            sys_state := NORMAL
            || load_kill_switch := SWITCH_OFF
        END
        ||
        // Updates system operation
        IF (load_user_switch = SWITCH_OFF or load_kill_switch = SWITCH_ON)
            & voltage < UNIT_ISSUE_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            & inputs_last_value(SOLAR_CELL_ARRAY)(VOLTAGE) > voltage
            //& inputs_last_value(SOLAR_CELL_ARRAY)(CURRENT) > 0
            & units_state(SOLAR_CELL_ARRAY) /= UNIT_CRITICAL
            
            & voltage < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE)
            & current < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
            & temperature < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            // Recharge battery when:
            //     - Load is OFF or is Killed by critical condition
            //     - Battery voltage is lower than battery ISSUE threshold
            //     - Solar Cell Array is producing any power with voltage over the battery voltage
            //     - Solar Cell Array is not on critical condition
            //     - Battery pack is not on critical state
            power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            ||
            IF battery_switch = SWITCH_OFF
			THEN
				battery_switch := SWITCH_ON
				|| charging_attempts_counts := max({5, charging_attempts_counts + 1})
			END
        ELSIF load_user_switch = SWITCH_ON
            & load_kill_switch = SWITCH_OFF
            
            & voltage >= BATTERY_PACK_MIN_VOLTAGE
            
            & voltage >= LOAD_VOLTAGE
            
            & inputs_last_value(SOLAR_CELL_ARRAY)(VOLTAGE) < LOAD_VOLTAGE
            & units_state(SOLAR_CELL_ARRAY) /= UNIT_CRITICAL
				
            & units_state(LOAD) /= UNIT_CRITICAL
            
            & voltage < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](VOLTAGE) 
            & current < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
            & temperature < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            // Supply power when:
            //     - Load is ON and is NOT Killed by critical condition
            //     - Battery voltage is higher than minimal battery voltage
            //     - Battery voltage is enough for the load
            //     - Solar Cell Array is voltage is lower than required by the load
            //     - Solar Cell Array is not on critical state
            //     - Load is not on critical condition
            //     - Battery pack is not on critical state
            power_mux := {BATTERY_PACK, LOAD}
            || battery_switch := SWITCH_ON
            || load_switch := SWITCH_ON
        ELSE
            // If no operations are avaiable for the battery, turn it off
            battery_switch := SWITCH_OFF
        END
        ||
        // Updates fan state
        IF temperature >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            fan_speed := FAN_HIGH
        ELSIF temperature >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](TEMPERATURE) 
        THEN
            fan_speed := FAN_MID
        ELSIF temperature > 0
        THEN
            fan_speed := FAN_LOW
        ELSE
            fan_speed := FAN_STOP
        END
    END;
    
    /*
     * Update input values for the Load
     *
     * Pre: The system must not be OFF nor in START state
     *      The unit must be a load
     *      The user must have turned the load on
     *      The current value must be a natural within the current range
     *      The difference between the previous and updated current values must not be greater than 100mA
     * 
     * Updates input values based for a unit
     */
    updateLoad(unit, current) =
    PRE
        sys_state /: {OFF, START}
        & unit = LOAD
        & load_user_switch = SWITCH_ON
        & current : NATURAL
        & current >= CURRENT_MIN 
        & current <= CURRENT_MAX 
        & current mod 100 = 0
        & (inputs_last_value(unit)(CURRENT) > current => inputs_last_value(unit)(CURRENT)-current <= 100)
        & (inputs_last_value(unit)(CURRENT) <= current => current-inputs_last_value(unit)(CURRENT) <= 100)
        & inputs_last_value(unit) /= {CURRENT |-> current}
        & (load_user_switch = SWITCH_OFF => current = 0)
    THEN
        // Updates unit sensor values
        inputs_last_value := inputs_last_value <+ {unit |-> {CURRENT |-> current}}
        ||
        // Updates unit current state
        IF current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT)
        THEN
            units_state := units_state <+ {unit |-> UNIT_CRITICAL}
        ELSIF current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            units_state := units_state <+ {unit |-> UNIT_ISSUE}
        ELSE
            units_state := units_state <+ {unit |-> UNIT_NORMAL}
        END
        ||
        // Updates system state based on current conditions
        IF UNIT_CRITICAL : units_state[UNIT - {unit}] 
            or current >= UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            // Critical state
            sys_state := CRITICAL
            || load_kill_switch := SWITCH_ON
        ELSIF UNIT_ISSUE : units_state[UNIT - {unit}]
            or current >= UNIT_ISSUE_LOWER_THRESHOLD[{unit}](CURRENT) 
        THEN
            // Issue state
            sys_state := ISSUE
            || load_kill_switch := SWITCH_OFF
        ELSE
            // Normal operation
            sys_state := NORMAL
            || load_kill_switch := SWITCH_OFF
        END
        ||
        // Updates system operation
        IF load_user_switch = SWITCH_ON 
            & load_kill_switch = SWITCH_OFF
            & current < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT) 
            & inputs_last_value(SOLAR_CELL_ARRAY)(VOLTAGE) >= LOAD_VOLTAGE
            & units_state(SOLAR_CELL_ARRAY) /= UNIT_CRITICAL
        THEN
            // Switch to solar cell supply:
            //     - Load is ON and NOT Killed by critical condition
            //     - Load current is not at the critical threshold
            //     - Solar Cell Array voltage is enough
            //     - Solar Cell Array is not on critical condition
            power_mux := {SOLAR_CELL_ARRAY, LOAD}
            || load_switch := SWITCH_ON
            || battery_switch := SWITCH_OFF
        ELSIF load_user_switch = SWITCH_ON 
            & load_kill_switch = SWITCH_OFF
            & current < UNIT_CRITICAL_LOWER_THRESHOLD[{unit}](CURRENT) 
            & inputs_last_value(BATTERY_PACK)(VOLTAGE) >= LOAD_VOLTAGE
            //& (inputs_last_value(BATTERY_PACK)(VOLTAGE)*inputs_last_value(BATTERY_PACK)(CURRENT)) >= (LOAD_VOLTAGE*current)
            & units_state(BATTERY_PACK) /= UNIT_CRITICAL
        THEN
            // Switch to battery supply:
            //     - Load is ON and NOT Killed by critical condition
            //     - Load current is not at the critical threshold
            //     - Battery Pack voltage is enough
            //     - Battery Pack is producing enough power
            //     - Battery Pack is not on critical condition
            power_mux := {BATTERY_PACK, LOAD}
            || load_switch := SWITCH_ON
            || battery_switch := SWITCH_ON
        ELSIF (load_user_switch = SWITCH_OFF or load_kill_switch = SWITCH_ON)
            
            & inputs_last_value(BATTERY_PACK)(VOLTAGE) < UNIT_ISSUE_LOWER_THRESHOLD[{BATTERY_PACK}](VOLTAGE)
            
            & inputs_last_value(SOLAR_CELL_ARRAY)(VOLTAGE) > inputs_last_value(BATTERY_PACK)(VOLTAGE)
			
            & units_state(BATTERY_PACK) /= UNIT_CRITICAL
            & units_state(SOLAR_CELL_ARRAY) /= UNIT_CRITICAL
        THEN
            // Recharge battery when:
            //     - Load is OFF or is Killed by critical condition
            //     - Battery voltage is lower than battery ISSUE threshold
            //     - Solar Cell Array voltage is higher than battery voltage
            //     - Solar Cell Array is not on CRITICAL conditions
            //     - Battery pack is not on CRITICAL conditions
            power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            ||
            IF battery_switch = SWITCH_OFF
			THEN
				battery_switch := SWITCH_ON
				|| charging_attempts_counts := max({5, charging_attempts_counts + 1})
			END
        ELSE
            // If no operations are avaiable for the load, turn it off
            load_switch := SWITCH_OFF
        END
    END;
    
    
    /*
     * User activated power supply
     *
     * Pre: The system must not be OFF nor in START state
     *      The load user switch must not be already ON
     * 
     * Turn the load ON (user view)
     */
    turnLoadOn =
    PRE
        sys_state /: {OFF, START}
        & load_user_switch /= SWITCH_ON
    THEN
        load_user_switch := SWITCH_ON
		|| load_switch := SWITCH_OFF
		|| battery_switch := SWITCH_OFF
    END;
    
    
    /*
     * User activated power supply
     *
     * Pre: The system must not be OFF nor in START state
     *      The load user switch must not be already OFF
     * 
     * Turn the load OFF (user view)
     */
    turnLoadOff =
    PRE
        sys_state /: {OFF, START}
        & load_user_switch /= SWITCH_OFF
    THEN
        load_user_switch := SWITCH_OFF
        || units_state := units_state <+ {LOAD |-> UNIT_NORMAL}
        || inputs_last_value := inputs_last_value <+ {LOAD |-> {CURRENT |-> 0}}
		|| 
		IF inputs_last_value(BATTERY_PACK)(VOLTAGE) < UNIT_ISSUE_LOWER_THRESHOLD[{BATTERY_PACK}](VOLTAGE)
            
            & inputs_last_value(SOLAR_CELL_ARRAY)(VOLTAGE) > inputs_last_value(BATTERY_PACK)(VOLTAGE)
			
            & units_state(BATTERY_PACK) /= UNIT_CRITICAL
            & units_state(SOLAR_CELL_ARRAY) /= UNIT_CRITICAL
        THEN
            // Recharge battery when:
            //     - Load is OFF or is Killed by critical condition
            //     - Battery voltage is lower than battery ISSUE threshold
            //     - Solar Cell Array voltage is higher than battery voltage
            //     - Solar Cell Array is not on CRITICAL conditions
            //     - Battery pack is not on CRITICAL conditions
            power_mux := {SOLAR_CELL_ARRAY, BATTERY_PACK}
            || load_switch := SWITCH_OFF
            ||
            IF battery_switch = SWITCH_OFF
			THEN
				battery_switch := SWITCH_ON
				|| charging_attempts_counts := max({5, charging_attempts_counts + 1})
			END
		END
    END
    
    
END
