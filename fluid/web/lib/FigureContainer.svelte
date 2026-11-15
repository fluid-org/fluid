<script lang="ts">
	import { onMount } from 'svelte';
	import './view-styles.css';

	let { draw } = $props();

	onMount(() => {
		draw('fig');
	});
</script>

<div id="fig">
	<div class="fig-loading">loading figure(s)</div>
</div>

<!-- CSS is scoped to the component and served only when
the component is rendered, i.e. not a single big .css file
for the whole site -->
<style>
	@keyframes fadeIn {
		from {
			opacity: 0;
		}
		to {
			opacity: 1;
		}
	}

	.fig-loading:only-child {
		color: fuchsia;
		animation: fadeIn 2s ease-in-out infinite alternate;
	}

	.fig-loading:not(:only-child) {
		display: none;
	}
</style>
