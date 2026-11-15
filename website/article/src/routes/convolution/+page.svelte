<script>
	import { CodeMirror, DataPane, FigureGraph, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Matrix convolution</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div id="fig-data-pane" class="data-pane">
			<div id="fig-input" class="flex-right-align data-pane-column"></div>
			<div id="fig-intermediate" class="flex-right-align intermediates"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<div class="flex-top-align">
			<FigureGraph graph="../graph/convolution.json" />
			<div></div>
		</div>
		<CodeMirror name="convolution" src="../src/convolution.fld" />
	</div>
</Grid>

<style>
	.data-pane {
		display: grid;
		grid-template-columns: min-content min-content;
		vertical-align: top;
		justify-content: end;
	}

	.data-pane * {
		font-size: 9pt;
	}

	:global(.intermediates .para-text) {
		margin-left: 5pt;
		margin-right: 3pt;
	}

   /* global can cause preload flicker so use sparingly  */
	:global(.intermediates:has(> *)) {
		border-right: 1px dotted #cccccc;
	}
</style>
