<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/non-renewables.json';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Non-Renewable Energy plots</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<FigureGraph {spec} graph="../graph/non-renewables.json" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 475px;
	}
</style>
