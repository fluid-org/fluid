<script>
	import { Figure, Grid } from '@fluid-org/fluid';

	const spec = {
		fluidSrcPath: ['../src', '../lib'],
		inputs: [],
		query: false,
		linking: false
	};
</script>

<Grid>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>Tick control</h3>
		<p>
			Illustrative decimal-year series with tick spacing set to Every and Count, and label formats
			set to Decimals.
		</p>
	</div>

	<div></div>

	<div class="flex-left-align">
		<Figure {spec} fld="../src/ticks.fld" />
	</div>
</Grid>
