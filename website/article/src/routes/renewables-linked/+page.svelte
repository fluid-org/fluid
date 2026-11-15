<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/renewables-linked.json';

	let showDataPane = false;

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
		<Figure {spec} fld="../src/bar_chart_line_chart.fld" />
	</div>
</Grid>
