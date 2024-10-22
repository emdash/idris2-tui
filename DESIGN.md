# Design #

This library is inspired mainly by Elm, but it's been heavily
influenced by feedback from the Idris compiler, as well as the Idris
community, which is most helpful.

The design is still in flux, but the goal is to allow for:

- suitable for rapid prototyping
- egonomic API
- soft landing for folks new to Idris
  - not requiring knowledge of too many concepts to get started.
  - build something interactive right away.
- explore programming with dependent types.

It's not quite there yet, except for that last one.

## MVC vs MVU ##

In classical MVC, a model is a stateful object. In contrast, this
library uses model-view-update.

The central notions are:

- *View*
- *Event*
- *Handler*
- *Component*

There are some libraries / embedded DSLs for writing views and
handlers.

Concretely, `View` is an *interface* which types can implement,
somewhat like `Show`.

`Component` is a dependent record type, which pairs an internal state
type with a compatible handler. Then there is a library of reusable
components which work on values of the `Component` type.

Then there is `MainLoop`, which contains the machinery required to run
a component as a UI.

## Geometry ##

Working with raw indices is annoying. This library provides:

- `Pos`   A 2D Point
- `Area`  A 2D Size
- `Rect`  A 2D Rectangle

Various operations are implemented on these which allow shifting,
scaling, and subdivision.

The math in this module is integer-based, as we're working with
character cells rather than geometric points. If you're experiencing
issues with layout, it's possible there's an off-by-one issue in this
library.

## Painting ##

- `Context` models the state of the terminal window
- Uses types from `TUI.Geometry`
- While `View`s can paint anywhere they want, a `window` is supplied
  for reference. Views can manipulate this rectangle and hand it off
  to subviews.

In comparison to ncurses, this library does direct drawing to the
terminal. And so, there are no intermediate buffers. Moreover, there
is no optimization of screen updates.

Instead of optimizing updates, I use
[iTerm2's synchronous updates](https://gitlab.com/gnachman/iterm2/-/wikis/synchronized-updates-spec).
This is protocol is ignored on unsupported terminals -- what you get
may or may not be usable, as you'll likely experience flicker.

I would like to support progressive enhancement, but I also want to
support things like sixel graphics. To do optimized updates on legacy
terminals, the library needs to buffer its output (in order to
calculate deltas). For sixel data this gets tricky.

I might include optional support for this style of rendering, if
there's demand for it, but I don't want to mandate it at the moment.

## Events ##

Right now there is only support for events of type `TUI.Key`. I hope
to add support for events of arbitrary type, but I might need some
help with this.

There's a `MainLoop` interface for handling events. The library
provides three mainloop implementations:

- `Base`: reads stdin directly using `getChar` from base.
- `InputShim`: decodes events as JSON records sent via stdin.
- `Default`: chooses between `Base` and `InputShim` at runtime.

My next priority is to implement a MainLoop on top of `idris2-linux`,
as the `Base` mainloop doesn't allow for any concurrency. Now that we
have `idris2-async`, and `idris2-uv`, it makes sense to include
mainloop impls for each of those, as well.

Events are hard-coded to be ANSI keys. This is a huge limitation of
the library at the moment. I could use help with that (hint hint).

## Components Produce Values ##

A value of type `Component a` may yield a value of type `a`.

When you call `runComponent`, the component will run until it yields a
value, at which point, the mainloop exits and returns the given value.

## Modal Components ##

When you use `runComponent`, there is an implicit stack of
components. You can push a new component with the `Push` / `push`
response. This top component will display until it yields a value. A
callback provided to the `push` response merges the value back into
the parent component.
