<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['..', '../../../lib'],
		inputs: ['nap3_actions', 'ccra3_risks'],
		query: true,
		linking: true,
		rowFilter: 'Relevant'
	};

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
</style>
