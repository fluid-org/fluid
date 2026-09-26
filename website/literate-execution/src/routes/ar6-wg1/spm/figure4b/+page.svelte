<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['.', '../../../lib'],
		inputs: ['ssp126Source', 'ssp245Source', 'ssp126preds', 'ssp245preds'],
		query: false,
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
		<Figure {spec} fld="figure4b.fld" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 400px;
	}
</style>
