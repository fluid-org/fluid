<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane}>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>CO2 concentration</h3>
		<p>Illustrative CO2 concentration with the y scale set to Auto, FromZero, Fixed and Padded.</p>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div id="fig-data-pane" class="flex-right-align data-pane">
			<div id="fig-input" class="data-pane-column"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<FigureGraph graph="../graph/co2.json" />
	</div>
</Grid>
