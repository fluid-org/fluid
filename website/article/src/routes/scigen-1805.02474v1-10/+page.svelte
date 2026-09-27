<script>
	import { DataPane, Figure, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['../lib'],
		inputs: ['tableData'],
		query: true,
		linking: true
	};

	const toggleDataPane = () => {
		showDataPane = !showDataPane;
	};
</script>

<Grid {showDataPane} textPaneWidth = '530px'>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>1805.02474v1-10</h3>
	</div>

	<DataPane {showDataPane} toggle={toggleDataPane}>
		<div class="flex-right-align data-pane">
			<div id="fig-input"></div>
		</div>
	</DataPane>

	<div class="flex-left-align">
		<Figure {spec} fld="../lib/_1805_02474v1_10.fld" />
	</div>
</Grid>

<style>
	.data-pane {
		max-width: 400px;
	}
</style>
