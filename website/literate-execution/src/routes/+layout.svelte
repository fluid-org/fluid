<script lang="ts">
	import '$shared/assets/css/styles.css';
	import '@fontsource/roboto/latin-300.css';
	import '@fontsource/roboto/latin-500.css';

	import { version } from '@fluid-org/fluid';
	import favicon from '$lib/assets/image/favicon.ico';

	let { children } = $props();
</script>

<svelte:head>
	<meta name="generator" content="Fluid {version}" />
	<link rel="icon" href={favicon} />
</svelte:head>


{@render children()}
