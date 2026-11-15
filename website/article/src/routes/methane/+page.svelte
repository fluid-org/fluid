<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/methane.json';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Methane</h3>
		<p>Methane emissions example</p>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div id="fig-data-pane" class="flex-right-align data-pane">
			<div id="fig-input" class="data-pane-column"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<FigureGraph {spec} graph="../graph/methane.json" />
	</div>
</Grid>
