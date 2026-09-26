<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['.', '../../../lib'],
		inputs: ['tableData', 'likelihoods'],
		query: true,
		linking: true
	};

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Table SPM.1</h3>
		<p>Recreation of the IPCC AR6 table SPM.1</p>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
			<p></p>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<Figure {spec} fld="table1.fld" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 400px;
	}
</style>
