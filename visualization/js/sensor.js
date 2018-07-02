var Sensor = (function(){
	var sensor = function(_unit, _type){
		var timer;
		var iterationCount = 0;
		var $this = this;
		
		this.STATE = 'NONE';
		this.unit = _unit;
		this.type = _type;
		
		var updateBatteryVoltage = function(){
			switch($this.STATE){
				case 'NONE': break;
				case 'START_RECHARGE':
					var inv_sigmoid_recharge = function(x){ return (x <= 0) ? 0 : Math.round(-Math.log(4/x - 1)+5); };
					iterationCount = inv_sigmoid_recharge($this.last_value[0][1]);
					$this.STATE = 'RECHARGE';
					break;
				case 'RECHARGE': 
					var sigmoid_recharge = function(x){ return (x >= 10) ? 4 : Math.round(4/(1+Math.exp(-x+5))); };
					
					bms.executeEvent({
						name: 'updateBatteryPack',
						predicate: 'unit=BATTERY_PACK&voltage='+sigmoid_recharge(iterationCount++)+'&current='+$this.last_value[1][1]+'&temperature='+$this.last_value[2][1]
					});
					
					break;
				case 'START_DISCHARGE': 
					var inv_sigmoid_discharge = function(x){ return (x >= 4) ? 0 : Math.round(5-Math.log(-4/(x-4)-1)); };
					iterationCount = inv_sigmoid_discharge($this.last_value[0][1]);
					$this.STATE = 'DISCHARGE';
					break;
				case 'DISCHARGE': 
					var sigmoid_discharge = function(x){ return (x >= 10) ? 0 : Math.round(4-4/(1+Math.exp(-x+5))); };
					
					bms.executeEvent({
						name: 'updateBatteryPack',
						predicate: 'unit=BATTERY_PACK&voltage='+sigmoid_discharge(iterationCount++)+'&current='+$this.last_value[1][1]+'&temperature='+$this.last_value[2][1]
					});
					
					break;
			}
		};
		
		this.update = function(){
			if($this.unit == 'BATTERY_PACK' && $this.type == 'VOLTAGE') updateBatteryVoltage();
		};
		
		this.init = function(){
			$this = this;
			
			if(this.unit == 'BATTERY_PACK' && this.type == 'VOLTAGE'){
				this.timer = window.setInterval(this.update, 3000);
							
				bms.observe('formula', {
					formulas: ['battery_switch', 'load_switch', 'load_kill_switch', 'inputs_last_value(BATTERY_PACK)'],
					translate: true,
					trigger: function(res) {
						$this.battery_switch = res[0];
						$this.load_switch = res[1];
						$this.load_kill_switch = res[2];
						$this.last_value = res[3];				
						
						if ($this.battery_switch == 'SWITCH_ON' && $this.load_switch == 'SWITCH_ON' && $this.load_kill_switch == 'SWITCH_OFF')
							$this.STATE = ($this.STATE != 'DISCHARGE') ? 'START_DISCHARGE' : $this.STATE;
						else if ($this.battery_switch == 'SWITCH_ON' && $this.load_switch == 'SWITCH_OFF')
							$this.STATE = ($this.STATE != 'RECHARGE') ? 'START_RECHARGE' : $this.STATE;
						else
							$this.STATE = 'NONE';
					}
				});
			}
			
			else if(this.unit == 'BATTERY_PACK' && this.type == 'CURRENT')
				bms.observe('formula', {
					formulas: ['inputs_last_value(BATTERY_PACK)', 'inputs_last_value(LOAD)(CURRENT)'],
					translate: true,
					trigger: function(res) {
						last_value_battery = res[0];		
						current = res[1];				
						
						bms.executeEvent({
							name: 'updateBatteryPack',
							predicate: 'unit=BATTERY_PACK&voltage='+last_value_battery[0][1]+'&current='+current+'&temperature='+last_value_battery[2][1]
						});
					}
				});
			
			else if(this.unit == 'SOLAR_CELL_ARRAY' && this.type == 'CURRENT')
				bms.observe('formula', {
					formulas: ['inputs_last_value(SOLAR_CELL_ARRAY)', 'inputs_last_value(LOAD)(CURRENT)'],
					translate: true,
					trigger: function(res) {
						last_value_solar = res[0];		
						current = res[1];				
						
						bms.executeEvent({
							name: 'updateSolarCellArray',
							predicate: 'unit=SOLAR_CELL_ARRAY&voltage='+last_value_solar[0][1]+'&current='+current
						});
					}
				});
		};
		
	};

	return sensor;
})();
