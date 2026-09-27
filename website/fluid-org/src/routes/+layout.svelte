<script lang="ts">
	import '$shared/assets/css/styles.css';
	import '@fontsource/roboto/latin-300.css';
	import '@fontsource/roboto/latin-500.css';
	import '@fontsource/fira-code/400.css';

	import { page } from '$app/state';
	import favicon from '$lib/assets/image/favicon.ico';
	import FluidLogo from '$lib/assets/image/fluid.png';
	import { headerLinks } from '$lib/config/nav';

	let { children } = $props();
</script>

<svelte:head>
	<link rel="icon" href={favicon} />
</svelte:head>


<div class="site-header">
	<div class="header-logo">
		<img class="fluid-logo" src={FluidLogo} width="150px" alt="Fluid logo" />
		<p class="fluid-subtitle">pure • pythonic • provenance-aware</p>
	</div>
	<div class="header-divider"></div>
	<div class="header-nav">
		<nav>
			<ul>
				{#each headerLinks as { url, title }, index (index)}
					<li class={page.route.id === url ? 'active-page' : ''}><a href={url}>{title}</a></li>
				{/each}
			</ul>
		</nav>
	</div>
	<div></div>
</div>

{@render children()}

<div class="site-footer">
	<div></div>
	<div></div>
	<div class="flex-left-align">
		<p>© Fluid Contributors 2019-2026</p>
	</div>
	<div></div>
</div>

<style>
	.fluid-logo {
		margin-bottom: 0;
	}

	.fluid-subtitle {
		margin-bottom: 0;
		margin-top: 0;
		font-size: 12pt;
	}

	.site-header, .site-footer {
		display: grid;
		background-color: #f0f0f0;
		width: 100%;
		grid-template-columns: 1fr var(--toggle-button-width) 800px 1fr;
		padding-top: 7px;
		padding-bottom: 7px;
	}

	.site-footer {
		margin-top: 10px;
	}

	.header-logo {
		display: flex;
		flex-direction: column;
		align-items: flex-end;
		justify-content: center;
		padding-right: 10px;
	}

	.header-divider {
		border-right: 1px solid #ccc;
	}

	.header-nav {
		display: flex;
		align-items: center;
		padding-left: 10px;
	}

	@media (max-width: 900px) {
		.site-header, .site-footer {
			display: flex;
			flex-direction: column;
			padding: 7px 1em;
			box-sizing: border-box;
			overflow: hidden;
		}

		.header-logo {
			align-items: flex-end;
			padding-right: 0;
			max-width: 100%;
			overflow: hidden;
		}

		.header-logo :global(img) {
			max-width: 100%;
			height: auto;
		}

		.header-divider {
			display: none;
		}

		.header-nav {
			padding-left: 0;
		}

		.header-nav :global(nav ul li) {
			float: none;
		}

		.header-nav :global(nav ul li:not(:last-child)::after) {
			display: none;
		}

		.site-header > div:last-child,
		.site-footer > div:last-child {
			display: none;
		}
	}
</style>
