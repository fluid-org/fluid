<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/figure4b.json';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Figure SPM.4b</h3>
		<p>Recreating the bar plots from IPCC AR6 Box SPM.4b</p>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
			<div id="fig-intermediate" class="flex-right-align intermediates"></div>
		</div>
	</DataPane>

	<div>
		<FigureGraph {spec} graph="../../../graph/figure4b.json" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 400px;
	}
</style>
