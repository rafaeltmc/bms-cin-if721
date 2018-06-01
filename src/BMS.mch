/* BMS
 */
MACHINE
    BMS
DEFINITIONS 
    "INPUTS.def"
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
VARIABLES
    sys_state,
    sys_start_missing_inputs,
    
    inputs_last_value    
INVARIANT
    sys_state : SYS_STATES
    & sys_start_missing_inputs <: dom(INPUTS)
    
    & inputs_last_value : dom(INPUTS) +-> NATURAL
    
    & sys_start_missing_inputs /\ dom(inputs_last_value) = {}
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
    END
    
END
