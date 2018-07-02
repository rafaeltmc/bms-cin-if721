var Sky = (function(){
	var stages = [
		'sky-very-dark-clouds.svg',
		'sky-dark-clouds.svg',
		'sky-clouds-lots.svg',
		'sky-clouds.svg',
		'sky-clear.svg'
	];
	
	var sky = function(){
	};
	
	sky.prototype.init = function(elementSelector){
		bms.observe('formula', {
			selector: elementSelector,
			formulas: ['inputs_last_value(SOLAR_CELL_ARRAY)(VOLTAGE)'],
			trigger: function(origin, res) {
				var voltage = parseInt(res[0]);
				origin.attr('data-voltage', voltage);
				origin.attr('xlink:href', 'images/'+sky.getStage(voltage));
			}
		});

		bms.executeEvent({
			selector: elementSelector,
			events: [
				{
					name: 'updateSolarCellArray',
					predicate: function(origin){
						var voltage = parseInt(origin.attr('data-voltage'));
						return 'unit=SOLAR_CELL_ARRAY&voltage='+(voltage+1)+'&current=0';
					}
				},
				{
					name: 'updateSolarCellArray',
					predicate: function(origin){
						var voltage = parseInt(origin.attr('data-voltage'));
						return 'unit=SOLAR_CELL_ARRAY&voltage='+(voltage-1)+'&current=0';
					}
				}
			],
			label: function(origin, event){
				params={};event.predicate.replace(/[?&]+([^=&]+)=([^&]*)/gi,function(s,k,v){params[k]=v})
				
				return 'Update Solar Cell Array Voltage to '+params['voltage'];
			}
		});
	};

	sky.getStage = function(voltage){
		if (voltage == 0) return stages[0];
		else if(voltage <= 1) return stages[1];
		else if(voltage <= 2) return stages[2];
		else if(voltage <= 3) return stages[3];
		else return stages[4];
	};
	
	return sky;
})();
