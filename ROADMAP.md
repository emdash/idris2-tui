# Limitations and Roadmap

Most of the limitations are down to planned features.

## No Buffering

This is a design limitation. See previous section.

What you lose without buffering is direct support for overlapping
windows. More tragically, there is no support for *clipping*, so it's
up to application code not render out-of-bounds. This also makes makes
scrolling components tricky to implement. There may be some
terminal-specific hacks to explore here.

And so, the drawing model favors a left-to-right, top-to-bottom
drawing order, which is robust against the inability to clip painting
to a specific region of the screen.

Fortunately, this dovetails with structural recursion. See `*split`,
and `*divide` in `TUI.Geometry` module. Or see `pack*` and `paint*` in
`TUI.View`. If you use these handy routines, you're on the garden
path.

The upside is that, since any `View` has complete freedom, you can do
things with layout that would be difficult or impossible in other
frameworks.

## Limited Key Handling

There's rudimentary ANSI decoding for basic keys. It's good enough to
at least start coding interactive things that run in your terminal,
but it's not yet enough to write a full-fledged application.

## Event Types are Hard Coded

The existing event types are hard-coded into the library mainloop and
input shim. The reason for this is that I can't figure out the best
way to generalize event handling without breaking other features of
the API that I think I like..

## <a name="kbd">Keyboard Input

I plan to support this standard for [unambigous keyboard
input](https://sw.kovidgoyal.net/kitty/keyboard-protocol/).

For now, if you want to send a literal escape, you must press escape
twice. This behavior will change as soon as I support the kitty
protocol, as I find it rather irritating.

Each breaking change will signal a point release.

When the full protocol is supported (including key report mode), I
will call it 1.0.

## Feature Detection

For the moment, there is no support for termcap, terminfo, ANSI query
strings, etc. Therefore, there is no mechanism to support graceful
degredation and / or fallback functionality. Supported terminals are
supported, all others are not.

## Localization, Internationalization, and Accessiblity

I hope to get to this at some point. And I aim to do a decent job when
I get to it. But it's only worth it to me if other people end up using
this, and it's just too soon to say.

## Compatibility Shim for Browsers

I can see no reason why this library couldn't eventually support
running in the browser, particularly with the help of an embedded
VTE. This could be an easy and fun way to create single page apps with
a certain nerdy aesthetic.
