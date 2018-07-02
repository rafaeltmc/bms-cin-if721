var CarControls = (function(){
	var carcontrols = function(){
	};
	
	var initStarStop = function(carStartStopSelector){
		bms.observe('formula', {
			selector: carStartStopSelector,
			formulas: ['load_user_switch'],
			trigger: function(origin, res) {
				var load_user_switch = res[0];
				switch (load_user_switch){
					case 'SWITCH_OFF': origin.attr('xlink:href', 'images/start-stop-off.svg'); break;
					default: origin.attr('xlink:href', 'images/start-stop-on.svg'); break;
				}
			}
		});

		bms.executeEvent({
			selector: carStartStopSelector,
			events: [
				{
					name: 'turnLoadOn',
					predicate: ''
				},
				{
					name: 'turnLoadOff',
					predicate: ''
				}
			],
			label: function(origin, event){
				switch (event.name){
					case 'turnLoadOn': return 'Turn car ON';
					case 'turnLoadOff': return 'Turn car OFF';
				}
			}
		});
	};
	
	var initPedals = function(carAcceleratorPedalSelector, carBreakPedalSelector){
		bms.observe('formula', {
			selector: carAcceleratorPedalSelector,
			formulas: ['inputs_last_value(LOAD)(CURRENT)'],
			trigger: function(origin, res) {
				var current = parseInt(res[0]);
				origin.attr('data-current', current);
			}
		});
		
		bms.observe('formula', {
			selector: carBreakPedalSelector,
			formulas: ['inputs_last_value(LOAD)(CURRENT)'],
			trigger: function(origin, res) {
				var current = parseInt(res[0]);
				origin.attr('data-current', current);
			}
		});
		
		bms.executeEvent({
			selector: carAcceleratorPedalSelector,
			events: [
				{
					name: 'updateLoad',
					predicate: function(origin){
						var current = parseInt(origin.attr('data-current'));
						return 'unit=LOAD&current='+(current+100);
					}
				}
			],
			label: function(origin, event){
				return "Accelerate";
			}
		});
		
		bms.executeEvent({
			selector: carBreakPedalSelector,
			events: [
				{
					name: 'updateLoad',
					predicate: function(origin){
						var current = parseInt(origin.attr('data-current'));
						return 'unit=LOAD&current='+(current-100);
					}
				}
			],
			label: function(origin, event){
				return "Break";
			}
		});
	};
	
	carcontrols.prototype.init = function(carStartStopSelector,
											carAcceleratorPedalSelector, 
											carBreakPedalSelector){
		initStarStop(carStartStopSelector);
		initPedals(carAcceleratorPedalSelector, carBreakPedalSelector);
	};

	return carcontrols;
})();
