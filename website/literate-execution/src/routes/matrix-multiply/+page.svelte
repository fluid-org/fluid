<script>
	import { DataPane, FigureSrc, Grid } from '@fluid-org/fluid';

	let showDataPane = false;

	const spec = {
		fluidSrcPath: ['../lib'],
		inputs: ['a', 'b', 'c'],
		query: true,
		linking: false
	};

	const src = `from fluid.matrix import mat_mul
from fluid.view import MultiView
from matrixMultiply.matrices import a, b, c

MultiView([
  mat_mul(mat_mul(a, b), c),
  mat_mul(a, mat_mul(b, c))
])`;

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
			<FigureSrc {spec} {src} />
			<div></div>
		</div>
	</div>
</Grid>

<style>
	.data-pane {
		display: grid;
		grid-template-columns: min-content min-content;
		vertical-align: top;
		justify-content: end;
	}

	:global(.intermediates:has(> *)) {
		border-right: 1px dotted #cccccc;
	}

	:global(.matrix-cell.selected-primary-persistent) {
		fill: rgb(214, 240, 214);
	}

	:global(.matrix-cell.selected-secondary-persistent) {
		fill: white;
	}

	:global(.matrix-cell-text.selected-primary-persistent:not(.matrix-cell-text.selected-primary-transient)) {
		color: green;
	}

	:global(
			.matrix-cell-text.selected-secondary-persistent:not(
					.matrix-cell-text.selected-primary-transient
				)
		),
	:global(
			.matrix-cell-text.selected-secondary-transient:not(
					.matrix-cell-text.selected-primary-persistent
				):not(.matrix-cell-text.selected-primary-transient)
		) {
		color: rgb(205, 205, 205);
	}
</style>
