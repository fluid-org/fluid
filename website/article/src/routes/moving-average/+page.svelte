<script>
	import { DataPane, FigureGraph, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane} textPaneWidth = '400px'>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Moving Average</h3>
		<p>
			The following chart shows a moving average (or rolling average) plot for methane emissions
			under projected emissions scenario
			<a href="https://en.wikipedia.org/wiki/Shared_Socioeconomic_Pathways">SSP5-8.5</a>.
		</p>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<p>
				Every <code>year</code> value is used in both the original curve and its moving average.
			</p>

			<div id="fig-input"></div>

			<p>
				With <code>emissions</code>, each value contributes to
				<span class="highlight">one</span> point in the original curve but
				<span class="highlight">three</span>
				in the moving average.
			</p>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<FigureGraph graph="../graph/moving-average.json" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 300px;
	}
</style>
