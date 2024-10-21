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

In classical MVC, a model is a stateful object. This is a
model-view-update approach.

The central notions are:

- *View*
- *Event*
- *Handler*
- *Component*

There are some libraries / embedded DSLs for writing views and
handlers.

Concretely, `View` is an *interface* which types can implement,
somewhat like `Show`. `Component` is a dependent record type, which
pairs an internal state type with a compatible handler. Then there is
a library of reusable components which work on values of the
`Component` type. Then there is `MainLoop`, which is all the machinery
required to run a component as a UI.

## Geometry ##

Working with raw indices is annoying. This library provides:

- `Pos`   A 2D Point
- `Area`  A 2D Size
- `Rect`  A 2D Rectangle

Various operations are implemented on these which allow shifting,
scaling, and subdivision.

## Painting ##

- `Context` models the state of the terminal window
- Uses types from `TUI.Geometry`
- While `View`s can paint anywhere they want, a `window` is supplied
  for reference. Views can manipulate this rectangle and hand it off
  to subviews.

In comparison to ncurses, this library does direct drawing to the
terminal. And so, there are no intermediate buffers. Moreover,
there is no optimization of screen updates.

Instead of optimizing updates, I use [Kitty's synchronous update
protocol]
(https://gitlab.com/gnachman/iterm2/-/wikis/synchronized-updates-spec).
This is protocol is ignored on unsupported terminals -- what you get
may or may not be usable.

I would like to support progressive enhancement, but I also want to
support things like sixel graphics. To do optimized updates on legacy
terminals, the library needs to buffer its output (in order to
calculate deltas). For sixel data this gets tricky.

I might include optional support for this style of rendering, if
there's demand for it, but I don't want to mandate it at the moment.

## Events ##

There's a `MainLoop` interface for handling events. The library
provides three mainloop implementations:

- `Base`: reads stdin directly using `getChar` from base
- `InputShim`: decodes events as JSON records sent via stdin.
- `Default`: chooses between `Base` and `InputShim` at runtime.

Events are hard-coded to be ANSI keys. This is a huge limitation of
the library at the moment. I could use help with that (hint hint).
