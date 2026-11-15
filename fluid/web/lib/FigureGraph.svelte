<script lang="ts">
	import { loadFigureGraph } from '../../output-es/App.LoadFigureGraph';
	import FigureContainer from './FigureContainer.svelte';

	let { graph } = $props();
</script>

<FigureContainer draw={(divId) => loadFigureGraph(divId)(graph)()} />
