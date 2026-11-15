<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/nap3-figure1-simplified.json';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane} textPaneWidth="350px">
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>NAP3/CCRA3 Assessment</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
			<div id="fig-intermediate" class="flex-right-align intermediates"></div>
		</div>
	</DataPane>

	<div>
		<FigureGraph {spec} graph="../../graph/nap3-figure1-simplified.json" />
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

	:global(#fig-intermediate .para-text) {
		display: inline;
	}

	:global(#fig-intermediate) {
		margin-top: 1em;
	}

	:global(#fig-output svg) {
		margin-top: 1em;
	}
</style>
