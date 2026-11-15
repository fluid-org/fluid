<script lang="ts">
	import { loadFigure } from '../../output-es/App.LoadFigure';
	import FigureContainer from './FigureContainer.svelte';

	let { spec, fld } = $props();
</script>

<FigureContainer draw={(divId) => loadFigure(spec)(divId)(fld)()} />
