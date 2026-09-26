<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['../lib'],
		inputs: ['nonRenewables'],
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
		<h3>Non-Renewable Energy plots</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<Figure {spec} fld="../lib/non_renewables.fld" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 475px;
	}
</style>
