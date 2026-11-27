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
		<h3>CO2 concentration</h3>
		<p>Illustrative CO2 concentration with the y scale set to Auto, FromZero and Fixed.</p>
	</div>

	<div></div>

	<div class="flex-left-align">
		<Figure {spec} fld="../src/co2.fld" />
	</div>
</Grid>
