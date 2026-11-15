<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['../src', '../lib'],
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
		<h3>Methane</h3>
		<p>Methane emissions example</p>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div id="fig-data-pane" class="flex-right-align data-pane">
			<div id="fig-input" class="data-pane-column"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<Figure {spec} fld="../src/methane.fld" />
	</div>
</Grid>
