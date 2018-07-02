var System = (function(){
	var system = function(){
	};
	
	var initSwitch = function(switchSelector){
		bms.observe('formula', {
			selector: switchSelector,
			formulas: ['sys_state'],
			trigger: function(origin, res) {
				var sys_state = res[0];
				
				if (sys_state == 'OFF') 
					origin.attr('xlink:href', 'images/system-off.svg');
				else
					origin.attr('xlink:href', 'images/system-on.svg');
			}
		});
		
		bms.executeEvent({
			selector: switchSelector,
			events: [
				{
					name: 'turnOn',
					predicate: ''
				},
				{
					name: 'turnOff',
					predicate: ''
				}
			],
			label: function(origin, event){
				switch (event.name){
					case 'turnOn': return 'Turn system ON';
					case 'turnOff': return 'Turn system OFF';
				}
			},
			callback: function(origin, data){
				if (data.name == 'turnOn'){
					bms.executeEvent({
						name: 'initializeSolarCellArray',
						predicate: 'unit=SOLAR_CELL_ARRAY&voltage=0&current=0'
					});
					bms.executeEvent({
						name: 'initializeBatteryPack',
						predicate: 'unit=BATTERY_PACK&voltage=0&current=0&temperature=0'
					});
					bms.executeEvent({
						name: 'initializeSingleBattery',
						predicate: 'unit=SINGLE_BATTERY_1&voltage=0&current=0'
					});
					bms.executeEvent({
						name: 'initializeSingleBattery',
						predicate: 'unit=SINGLE_BATTERY_2&voltage=0&current=0'
					});
					bms.executeEvent({
						name: 'initializeLoad',
						predicate: 'unit=LOAD&current=0'
					});
				}
			}
		});
	};
	
	var initSystemState = function(stateSelector){
		bms.observe('formula', {
			selector: stateSelector,
			formulas: ['sys_state'],
			trigger: function(origin, res) {
				var sys_state = res[0];
				
				switch (sys_state){
					case 'OFF': origin.attr('xlink:href', 'images/sys-state-off.svg'); break;
					case 'ISSUE': origin.attr('xlink:href', 'images/sys-state-issue.svg'); break;
					case 'CRITICAL': origin.attr('xlink:href', 'images/sys-state-critical.svg'); break;
					default: origin.attr('xlink:href', 'images/sys-state-normal.svg'); break;
				}
			}
		});
	};
	
	var initPowerSource = function(solarPowerSelector, batteryPowerSelector){
		bms.observe('formula', {
			selector: solarPowerSelector,
			formulas: ['power_mux', 'battery_switch', 'load_switch', 'load_kill_switch'],
			trigger: function(origin, res) {
				power_mux = res[0];
				battery_switch = res[1];
				load_switch = res[2];
				load_kill_switch = res[3];
				
				if (power_mux.includes('SOLAR_CELL_ARRAY') && (battery_switch == 'SWITCH_ON'|| load_switch == 'SWITCH_ON') && load_kill_switch == 'SWITCH_OFF')
					origin.attr('xlink:href', 'images/solar-power-on.svg');
				else
					origin.attr('xlink:href', 'images/solar-power-off.svg');
			}
		});
		
		bms.observe('formula', {
			selector: batteryPowerSelector,
			formulas: ['battery_switch', 'load_switch', 'load_kill_switch'],
			trigger: function(origin, res) {
				battery_switch = res[0];
				load_switch = res[1];
				load_kill_switch = res[2];
				
				if (battery_switch == 'SWITCH_OFF' || (load_kill_switch == 'SWITCH_ON' && load_switch == 'SWITCH_ON'))
					origin.attr('xlink:href', 'images/battery-power-off.svg');
				else if (load_switch == 'SWITCH_ON')
					origin.attr('xlink:href', 'images/battery-power-on.svg');
				else
					origin.attr('xlink:href', 'images/battery-recharging.svg');
			}
		});
	};
	
	system.prototype.init = function(switchSelector, 
										stateSelector,
										solarPowerSelector, 
										batteryPowerSelector){
		initSwitch(switchSelector);
		initSystemState(stateSelector);
		initPowerSource(solarPowerSelector, batteryPowerSelector);
		
	};
	
	return system;
})();
