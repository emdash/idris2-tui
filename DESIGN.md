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

## Overview

In classical MVC, a model is a stateful object. In contrast, this
library uses model-view-update. States are immutable, and updates are
expressed via pure functions.

The central notions are:

### *State*

The complete state of your application. Changes to state should be
expressed as pure functions.

### *View*

`View` is an interface for drawing to the screen. Types which
implement `View` are called *views*.

### *Event*

User input, such as a key press or mouse movement.

### *Handler*

A pure function which updates application state in response to an
event.

### *Component*

A high level notion which unifies *state*, *view*, and *handler* into
a single value that can be composed with other components.

## Events

Right now there is only support for events of type `TUI.Key`. I would
really like to allow support for events of arbitrary type, but am not
sure how to do it. I have tried a couple times, but it seems to really
pollute the API, or else lead to problems with type checking.

Note: If you think you can help with this, please open an issue and
explain your approach. I'm open to breaking changes that will remove
this limitation.

There's a `MainLoop` interface for handling events. The library
provides three mainloop implementations:

- `Base`: reads stdin directly using `getChar` from base.
- `InputShim`: decodes events as JSON records sent via stdin.
- `Default`: chooses between `Base` and `InputShim` at runtime.

### Async Events ###

Both `Base` and `InputShim` (and therefore `Default`) block reading on
stdin.

A MainLoop built on top of `idris2-linux` is certainly possible, and
would allow for a non-blocking event loop, which would be useful for a
variety of reasons.

However, until the `Component` library supports events of arbitrary
type, there isn't much of a point in having an async event loop, as
there's no way to deliver such events to these components.

### ANSI Key Sequences ###

One aspect of event handling I know how to support is ANSI key
sequence decoding. I just haven't got around to implementing the full
spec. Expect breaking changes to the `Key` type as I add support for
function, modifier keys, and other miscellaneous keys.

See also: this section in the [Roadmap](ROADMAP.md#kbd)

## Geometry ##

Working with raw row-major coordinates is annoying. This library
provides:

- `Pos`   A 2D Point
- `Area`  A 2D Size
- `Rect`  A 2D Rectangle

Various operations are implemented on these which allow shifting,
scaling, and subdivision, and painting using geometric values.

The math in this module is integer-based, and sometimes a little
confusing. We're working with character cells rather than geometric
points. If you're experiencing issues with layout, it's possible
there's an off-by-one issue in this library.

If you stick to using the `pack*` family of functions for layout, you
should not have to worry too much about this.

## Painting ##

- `Context` models the state of the terminal window
- Uses types from `TUI.Geometry`

In comparison to ncurses, this library does direct drawing to the
terminal. And so, there are no intermediate buffers. Moreover, there
is no optimization of screen updates. If all you want to do is direct
rendering, you can just use the routines in `Painting` to get the job
done. Use `runRaw` in `MainLoop` to pass in an explicit rendering

Instead of optimizing updates, I use: [iTerm2's synchronous updates](
https://gitlab.com/gnachman/iterm2/-/wikis/synchronized-updates-spec
). Right now this is hard-coded, and there's no feature detection for
it. Consider support for synchronized updates a soft requirement of
the library for now.

The said protocol is ignored on unsupported terminals -- what you get
may or may not be usable: the more bytes written to standard out, the
more likely you will experience flicker. This is why libraries like
ncurses do differential updates.

Why not do differential updates, then? Well, I don't want to have to
buffer the output just yet. I want to explore sixels, 24-bit color,
and other experimental features before I commit to the complexity and
overhead of buffering output.

Painting is fundamentally procedural, and painting order matters!

## View ##

`View` is an interface that's like 2D version of `Show`. A view
knows how to paint itself into a terminal `Context`, in one of a fixed
number of `State`s, and within a given `Rect`.

That views stay within bounds is `*not*` enforced by this library, as
there's no mechanism for it (see above). I may try to enforce this
later, if I can think of the right mechanism with which to do so. For
now, `View` implementations should try their best to voluntarily stay
in bounds.

A view can be drawn in an arbitrary window. A view should do its best
to scale, responsively, into this window. If a library View
implementation fails to scale responsibly, please open an
issue. Likewise, if you can justify a good *exception* to this rule,
please open an issue.

## Layout ##

The `Layout` module provides a family of functions for automatically
aranging `View`s on screen. These rely on `View`s correctly reporting
their `size`, so be sure and test your `View` implementations against
these functions.

## Components ##

A component compbines a `View`able state and a key event handler.

The library provides a family of components which implement common
keyboard UI patterns, as well as some higher-order components
(e.g. `Form`) which allow for composition of components.

You can also define your own custom components.

The main purpose of a `Component` is to produce a value of some
concrete type. So, for example, a confirmation dialog might yield a
`Bool`, while a spinner might yield a `String` or an element of a
finite set, while a A form component might construct an entire record.

Components exist for:
- entering data
- choosing items from a list
- managing lists of values

Some higher order components take a user-provided key handler, or may
broadcast key vents to multiple subcomponents. In such cases, one
needs to be aware of the the possibility of key collisions, and either
guard against it, or exploit it.

Components can also compose as *modally*, via the
semantically-blocking `push` / `Push` response.

## Feature Detection / Progressive {Enhancement / Graceful Degredation}  ##

I would like to support this, but only after the library design has
stablized somewhat.

Until then there's no support for it whatever. Keep your target
audience in mind when deciding what features to target. VTEs generally
ingore escape sequences they don't understand, but not always.

If you're trying to build a low-level OS tool, don't assume much more
than what the linux console provides. If you're building something
more developer focused, you can probably assume something on par with
iTerm2. End users generally rely on the default terminal emulator, and
are probably the hardest to support.
