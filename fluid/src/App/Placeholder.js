"use strict"

function placeholder(divId) {
   return document.querySelector(`#${divId} > .fig-loading`)
}

export function figureLoaded(divId) {
   return () => placeholder(divId)?.remove()
}

export function figureFailed(divId) {
   return msg => () => {
      const el = placeholder(divId)
      if (el) {
         el.className = "fig-error"
         el.textContent = msg
      }
   }
}
