"use strict"

import * as d3 from "d3"

// TODO: Drop this in favour of static "attrs" function (and similarly for "styles").
d3.selection.prototype.attrs = function(m) {
   for (const k in m) {
      this.attr(k, m[k])
   }
   return this
}

d3.selection.prototype.styles = function(m) {
   for (const k in m) {
      this.style(k, m[k])
   }
   return this
}

function computed (element, prop) {
   return window.getComputedStyle(element, null).getPropertyValue(prop);
}

// Should be always defined
function canvasFont (el) {
   return `${computed(el, 'font-weight')} ${computed(el, 'font-size')} ${computed(el, 'font-family')}`
}

function assertNonEmpty (sel) {
   if (sel.empty()) {
      throw new Error("Assertion failed: D3 selection is empty")
   }
}

// Could assume a div in document set up for this purpose. Pure; side-effects should be unobservable.
// Not especially reliable as might not inherit in situ styling that the actual text will
export function textDimensions (class_) {
   return text => {
      const element = document.createElement('text')
      element.textContent = text
      element.classList.add(class_)
      element.style.visibility = 'hidden'
      document.body.appendChild(element)

      const canvas = textDimensions.canvas || (textDimensions.canvas = document.createElement("canvas")) // re-use canvas
      const context = canvas.getContext("2d")
      context.font = canvasFont(element)
      const width = Math.ceil(context.measureText(text).width)
      const height = Math.ceil(element.offsetHeight)
      element.remove()
      return { width, height }
   }
}

export function createChild (parent) {
   return elementType => {
      return as => {
         return () => {
            return attrs(parent.append(elementType))(as)()
         }
      }
   }
}

export function createText (parent) {
   return text => {
      return () => {
        return parent.append(() => {
          return document.createTextNode(text)
        })
      }
   }
}

export function remove (element) {
   return () => {
      element.remove()
   }
}

export function line (to) {
   return points => {
      const line = d3.line()
         .x(d => to.x(d.x))
         .y(d => to.y(d.y))
      return line(points)
   }
}

// Axis with approximate tick count or exact tick values, and labels to given decimal places
function axis (d3Axis) {
   return count => {
      return values => {
         return places => {
            return parent => {
               return () => {
                  const ticked = values === null ? d3Axis.ticks(count) : d3Axis.tickValues(values)
                  return parent.call(ticked.tickSizeOuter(0).tickFormat(places === null ? d => d : d3.format(`.${places}f`)))
               }
            }
         }
      }
   }
}

export function xAxis (to) {
   return axis(d3.axisBottom(to.x))
}

export function yAxis (to) {
   return axis(d3.axisLeft(to.y))
}

export function numericXAxis (scale) {
   return parent => () => parent.call(d3.axisBottom(scale).tickSizeOuter(0))
}

export function numericYAxis (scale) {
   return parent => () => parent.call(d3.axisLeft(scale).tickSizeOuter(0))
}

export function setText (string) {
   return sel => {
      return () => {
         return sel.text(string)
      }
   }
}

// stateful but purify by allocating once
const colorScale_ = {
   schemePastel1: d3.scaleOrdinal(d3.schemePastel1),
   schemeAccent: d3.scaleOrdinal(d3.schemeAccent)
}

// TODO: better name
export function colorScale (scheme) {
   return key => {
      return colorScale_[scheme](key)
   }
}

export function dimensions (sel) {
   return () => {
      if (sel.nodes().length != 1) {
         throw "Expected singleton selection"
      }
      const [ node ] = sel.nodes()
      let { width, height } = node.getBBox()
      return { width: Math.ceil(width), height: Math.ceil(height) }
   }
}

export function isEmpty (sel) {
   return () => {
      return sel.empty()
   }
}

export function rootSelect (selector) {
   return () => {
      return d3.select(selector)
   }
}

export function select (selector) {
   return sel => {
      assertNonEmpty(sel)
      return () => {
         return sel.select(selector)
      }
   }
}

export function selectAll (selector) {
   return sel => {
      return () => {
         const sels = [];
         sel.selectAll(selector).each(function () {
            sels.push(d3.select(this))
         })
         return sels
      }
   }
}

// Similar to d3-selection-multi function of the same name.
export function attrs (sel) {
   return attrs => {
      return () => {
         if (typeof attrs == 'function') {
            return sel.each(function (d) {
               const attrs_ = attrs(d)
               const sel_ = d3.select(this)
               for (const k in attrs_) {
                  sel_.attr(k, attrs_[k])
               }
            })
         } else {
            for (const k in attrs) {
               sel.attr(k, attrs[k])
            }
            return sel
         }
      }
   }
}

export function styles (sel) {
   return styles => {
      return () => {
         return sel.styles(styles)
      }
   }
}

export function classed (classes) {
   return hasClass => {
      return sel => {
         return () => {
            return sel.classed(classes, hasClass)
         }
      }
   }
}

export function scaleLinear (x1) {
   return x2 => {
      return d3.scaleLinear().domain([x1.min, x1.max]).range([x2.min, x2.max])
   }
}

export function scaleBand (width) {
   return stackedBars => {
      return d3.scaleBand()
         .range([0, width])
         .domain(stackedBars)
         .padding(0.2)
   }
}

export function bandwidth (x) {
   return x.bandwidth()
}

export function datum (sel) {
   return () => {
      return sel.datum()
   }
}

export function setDatum (d) {
   return sel => {
      return () => {
         return sel.data([d]) // must be an array of data, even for singleton selection
      }
   }
}

export function on (eventType) {
   return listener => {
      return sel => {
         assertNonEmpty(sel)
         return () => {
            return sel.on(eventType, e => {
               if (e.button == 0) { // assumes e is a mouse event, which is the case for now
                  listener(e)
               }
            })
         }
      }
   }
}
