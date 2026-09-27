<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['..', '../../../lib'],
		inputs: ['nap3_actions'],
		query: true,
		linking: false,
		rowFilter: 'Relevant'
	};

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
		<Figure {spec} fld="figure1.fld" />
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
