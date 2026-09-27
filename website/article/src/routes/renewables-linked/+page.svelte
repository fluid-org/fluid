<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['../lib'],
		inputs: ['renewables'],
		query: false,
		linking: true
	};

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div>
		<h3>Non-renewable energy output</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div id="fig-data-pane" class="flex-right-align data-pane">
			<div id="fig-input" class="data-pane-column"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<Figure {spec} fld="../lib/bar_chart_line_chart.fld" />
	</div>
</Grid>
