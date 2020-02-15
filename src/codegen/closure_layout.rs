use smallvec::{smallvec, SmallVec};

use base_analysis::{ScopeId, ScopeMap, VariableType};
use lang_constructs::LangVariable;

pub(super) fn get_closure_layout<'a>(scope_map: &'a ScopeMap) -> Vec<Option<ClosureLayout<'a>>> {
    let mut entries = Vec::with_capacity(scope_map.scope_count());

    for scope_id in scope_map.scopes() {
        let to_add = ClosureLayout::new(scope_map, scope_id, &mut entries);
        entries.push(to_add);
    }

    entries
}

type LocalSlot<'prog> = &'prog LangVariable<'prog>;

#[derive(Default, Debug)]
pub(super) struct CaptureSlot<'prog> {
    scope_id: ScopeId,
    path: SmallVec<[u32; 4]>,
    accesses: SmallVec<[(LocalSlot<'prog>, usize); 4]>,
}

#[derive(Default, Debug)]
pub(super) struct ClosureLayout<'prog> {
    scope_id: ScopeId,
    local: SmallVec<[LocalSlot<'prog>; 4]>,
    capture: SmallVec<[CaptureSlot<'prog>; 4]>,
}

impl<'prog> ClosureLayout<'prog> {
    fn new(
        scope_map: &'prog ScopeMap,
        scope_id: ScopeId,
        prior: &mut [Option<Self>],
    ) -> Option<Self> {
        let mut local_slots = scope_map
            .get_owned_vars_for_scope(scope_id)
            .filter_map(|(v, t)| if t.is_closure() { Some(v) } else { None })
            .collect::<SmallVec<_>>();

        local_slots.sort();
        let local_slots = local_slots;

        let mut capture_slots = SmallVec::<[CaptureSlot; 4]>::new();

        for (var, t) in scope_map.get_used_vars_for_scope(scope_id) {
            let target_scope = match t {
                VariableType::Closure(s) if s != scope_id => s,
                _ => continue,
            };

            let idx = capture_slots
                .binary_search_by(|x| x.scope_id.cmp(&target_scope))
                .unwrap_or_else(|idx| {
                    let path =
                        ClosureLayout::trace_captures(scope_map, scope_id, target_scope, prior);

                    capture_slots.insert(
                        idx,
                        CaptureSlot {
                            scope_id: target_scope,
                            path,
                            accesses: SmallVec::new(),
                        },
                    );

                    idx
                });

            let target_local_idx = prior[target_scope as usize]
                .as_ref()
                .expect("target-scope closure")
                .local
                .binary_search(&var)
                .expect("target-scope closure local");

            let accesses = &mut capture_slots[idx].accesses;
            match accesses.binary_search_by_key(&var, |(v, _local_idx)| v) {
                Ok(i) => assert_eq!(accesses[i].1, target_local_idx),
                Err(i) => accesses.insert(i, (var, target_local_idx)),
            }
        }

        if local_slots.is_empty() && capture_slots.is_empty() {
            None
        } else {
            Some(ClosureLayout {
                scope_id,
                local: local_slots,
                capture: capture_slots,
            })
        }
    }

    fn trace_captures(
        scope_map: &ScopeMap,
        scope_id: ScopeId,
        target_scope_id: ScopeId,
        prior: &mut [Option<Self>],
    ) -> SmallVec<[u32; 4]> {
        let intermediate: SmallVec<[ScopeId; 4]> = scope_map
            .get_ancestor_scopes(scope_id)
            .take_while(|&s| s != target_scope_id)
            .collect();

        let mut path = smallvec![];

        for ancestor in intermediate.into_iter().rev() {
            let capture_idx = match &mut prior[ancestor as usize] {
                entry @ None => {
                    *entry = Some(ClosureLayout {
                        capture: smallvec![CaptureSlot {
                            scope_id: target_scope_id,
                            path,
                            ..CaptureSlot::default()
                        }],
                        ..ClosureLayout::default()
                    });

                    0
                }
                Some(layout) => match layout
                    .capture
                    .binary_search_by_key(&target_scope_id, |slot| slot.scope_id)
                {
                    Ok(idx) => idx,
                    Err(idx) => {
                        let to_insert = CaptureSlot {
                            scope_id: target_scope_id,
                            path,
                            ..CaptureSlot::default()
                        };

                        layout.capture.insert(idx, to_insert);
                        idx
                    }
                },
            };

            path = smallvec![capture_idx as u32];
        }

        path
    }

    pub fn get_local_offset(&self, var: &LangVariable) -> usize {
        self.local
            .binary_search(&var)
            .expect("missing closure local target")
    }

    pub fn get_capture_offset(&self, scope_id: ScopeId, var: &LangVariable) -> (usize, usize) {
        let capture_idx = self.get_capture_block_offset(scope_id);
        let capture_slot = &self.capture[capture_idx];

        let access_idx = capture_slot
            .accesses
            .binary_search_by_key(&var, |(v, _local_idx)| v)
            .expect("missing capture closure target");

        let (_, src_idx) = capture_slot.accesses[access_idx];

        (capture_idx, src_idx)
    }

    pub fn get_capture_block_offset(&self, scope_id: ScopeId) -> usize {
        self.capture
            .binary_search_by_key(&scope_id, |slot| slot.scope_id)
            .expect("missing capture closure target")
    }

    pub fn locals<'a>(&'a self) -> impl ExactSizeIterator<Item = &'a LocalSlot<'prog>> {
        self.local.iter()
    }

    pub fn captures(&self) -> impl ExactSizeIterator<Item = ScopeId> {
        // Hack: can't return the iterator directly because it ties up the 'prog
        // lifetime in a way Rust won't allow
        self.capture
            .iter()
            .map(|&CaptureSlot { scope_id, .. }| scope_id)
            .collect::<SmallVec<[ScopeId; 4]>>()
            .into_iter()
    }

    pub fn capture_accesses<'a>(
        &'a self,
    ) -> impl ExactSizeIterator<Item = (ScopeId, impl ExactSizeIterator<Item = &'a LocalSlot<'prog>>)>
    {
        self.capture.iter().map(
            |&CaptureSlot {
                 scope_id,
                 ref accesses,
                 ..
             }| { (scope_id, accesses.iter().map(|(v, _)| v)) },
        )
    }
}
