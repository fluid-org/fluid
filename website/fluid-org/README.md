# f.luid.org in SvelteKit

A rough clone of `website/fluid-org` in SvelteKit. SvelteKit is a Javascript framework for building/serving sites with many features, but here we are mostly taking advantage of components/templating and the Vite build system, which reduces and chunks up a lot of the Javascript dependencies.

I have made some minor tweaks (e.g. scoping some CSS to components, optimising images and removing external runtime dependencies like Font Awesome).

Loading the homepage produced here requires 1.10MB (398kB compressed) vs 2.08MB (637.09kB) on the current site. This is mostly due to Vite reducing the main Javascript bundle size. Furthermore, the Javascript bundle (and other shared scripts and styles) are not reloaded on navigation within the site.

## Quickstart

```sh
git clone https://github.com/jacobpake/fluid-website-sveltekit
yarn install
yarn run dev
```

This will print a URL to preview the website. The site will automatically refresh if you make any changes inside of the `src` directory.

### Building

Running `yarn run build` will create/update the `build` directory with the static build output. You can publish this anywhere that serves static files or run a preview server with `yarn run preview`.

## SvelteKit

This is a SvelteKit website. We are prerendering every page so in the build output there should be no server side functionality.

Svelte has good state management / reactivity, which would be [useful for visualisations](https://datavisualizationwithsvelte.com/#why-svelte-and-d3), but we do not take advantage of this here.

### Routing

Paths are defined using directory names in `src/routes`. The `index.html` equivalent inside a route directory is the `+page.svelte` file. The file `src/routes/convolution/+page.svelte` should produce a HTML response accessible at `https://f.luid.org/convolution`.

### Components

Components define some shared functionality and can be imported and rendered with arguments to other `.svelte` files. For example, the shared `FigureGraph.svelte` component is defined as:

```.svelte
<script lang="ts">
	import { loadFigureGraph } from '../../output-es/App.LoadFigureGraph';
	import FigureContainer from './FigureContainer.svelte';

	let { spec, graph } = $props();
</script>

<FigureContainer draw={(divId) => loadFigureGraph(spec)(divId)(graph)()} />
```

The component is used in other components or routes like:

```.svelte
<div class="some-other-html">
    <FigureGraph spec={mySpec} graph="../graph/example.json" />
</div>
```

`FigureContainer` calls `draw` in `onMount`, so a figure is drawn in the browser and not during server-side rendering (otherwise we would run into issues trying to update the DOM in a Node.js process).

The file named by `graph` is a figure graph. Before the site is built, `fluid build` evaluates the program named in the options file of the figure. The command then writes the figure graph. A visitor to the website only draws and queries the figure.

### Assets

Static assets can be kept in the `static` directory and will be served publicly where `static/fluid/non-renewables.fld` will be accessible from `https://f.luid.org/fluid/non-renewables.fld`.

If we prefer, we can keep assets in our `src/lib/assets` directory and import them into components. This enables Vite to do some extra processing, hashing, chunking, adding headers (if running on the server) that support better caching, performance etc. It will even inline them into the HTML if small enough and considered beneficial.

### Further reading and examples

- [Svelte docs](https://svelte.dev/docs/svelte/overview)
- [SvelteKit docs](https://svelte.dev/docs/kit/introduction)
- [Some visualisation examples with Svelte code](https://threlte.xyz/docs/examples/geometry/rendering-points)
- [Another library with examples](https://layercake.graphics/example/CirclePackForce)
- [Prerendered visualisations no JS](https://pancake-charts.surge.sh/)
- [More visualisation example](https://matterviz.janosh.dev/)
- [Live mermaid chart editor](https://mermaid.live)
