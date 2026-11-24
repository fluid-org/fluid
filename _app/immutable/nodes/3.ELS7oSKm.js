import{a as o,f as s}from"../chunks/BYli-BKX.js";import"../chunks/DZGnjdGz.js";import{n as i}from"../chunks/C9phqoAQ.js";import{G as r}from"../chunks/CFpeLg7H.js";var n=s(`<div></div> <div></div> <div class="flex-left-align"><h3 class="title">Frequently Asked Questions</h3> <p><span class="faq-question svelte-1bex8oj">How does Fluid work?</span> When you load a Fluid visualisation, the
			interpreter builds a <span class="highlight">dependence graph</span> capturing how data flows through
			the program. This graph is used to add various interactions to the chart (so that, for example,
			selecting an element in the output highlights the corresponding parts of the input). See our <a href="https://arxiv.org/abs/2403.04403">ESOP 2025 preprint</a> for details.</p> <p><span class="faq-question svelte-1bex8oj">Why not do this for Python/R/Julia?</span> Fine-grained dependency
			tracking for Python or R would be difficult: both languages have key libraries that depend heavily on
			C. Julia has less of a C dependency and could be a feasible target, although it would still probably
			require modifying the interpreter. Our approach is to develop a pure functional dialect of Python,
			for which we can then provide our own version of libraries like <code>numpy</code>.</p> <p><span class="faq-question svelte-1bex8oj">What's next for the language?</span> Most likely a gradual type system, better tooling and performance improvements.</p></div>`,1);function f(e){r(e,{showDataPane:"false",children:(a,l)=>{var t=n();i(4),o(a,t)},$$slots:{default:!0}})}export{f as component};
