(** * State events.

    [stateE S] ([Get : stateE S S], [Put : S -> stateE S unit]), the triggers
    [get]/[put] (under [stateE S -< E]) and the handler [h_state] all come from
    the [ctrees] library ([CTree.Interp.FoldStateT]), re-exported through
    [TICL.CTree.Core]. This module only exists as an import anchor. *)
From TICL Require Export CTree.Core.
