<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/scigen-1805.02474v1-10.json';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane} textPaneWidth = '530px'>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>1805.02474v1-10</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<FigureGraph {spec} graph="../graph/scigen-1805.02474v1-10.json" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 400px;
	}
</style>
