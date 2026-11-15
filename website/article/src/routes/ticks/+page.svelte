<script>
	import { FigureGraph, Grid } from '@fluid-org/fluid';
	import spec from '$lib/spec/ticks.json';

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
		<FigureGraph {spec} graph="../graph/ticks.json" />
	</div>
</Grid>
