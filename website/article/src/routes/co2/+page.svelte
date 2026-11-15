<script>
	import { FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/co2.json';

</script>

<Grid>
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<h3>CO2 concentration</h3>
		<p>Illustrative CO2 concentration with the y scale set to Auto, FromZero, Fixed and Padded.</p>
	</div>

	<div></div>

	<div class="flex-left-align">
		<FigureGraph {spec} graph="../graph/co2.json" />
	</div>
</Grid>
