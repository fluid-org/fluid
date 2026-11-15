<script lang="ts">
	import { loadFigureGraph } from '../../output-es/App.LoadFigureGraph';
	import FigureContainer from './FigureContainer.svelte';

	let { spec, graph } = $props();
</script>

<FigureContainer draw={(divId) => loadFigureGraph(spec)(divId)(graph)()} />
