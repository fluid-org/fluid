<script lang="ts">
	import { loadFigureSrc } from '../../output-es/App.LoadFigure';
	import FigureContainer from './FigureContainer.svelte';

	let { spec, src } = $props();
</script>

<FigureContainer draw={(divId) => loadFigureSrc(spec)(divId)(src)()} />
