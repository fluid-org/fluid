<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane} textPaneWidth="675px">
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Independent Assessment of National Adaptation Programme (NAP3)</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
			<div id="fig-intermediate" class="flex-right-align intermediates"></div>
		</div>
	</DataPane>

	<div>
		<FigureGraph graph="../../graph/nap3-figure1.json" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 400px;
	}

	:global(.table-cell.selected-primary-persistent) {
		background-color: rgb(236, 236, 236);
	}

	:global(.table-cell.selected-primary-transient) {
		color: black;
		background-color: rgb(230, 230, 255);
	}

	:global(.table-cell.selected-primary-transient.table-cell.selected-primary-persistent) {
		color: black;
		background-color: rgb(213, 213, 236);
	}
</style>
