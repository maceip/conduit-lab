import { useStudio } from '../state';
import { TURBOPROP_LEVELS, turboprop } from './turboprop';
import { MAGLEV_LEVELS, maglev } from './maglev';
import type { MachineDef } from './types';

/**
 * Machine registry — strictly the two CONDUIT engineering plates:
 *   1. Turboprop Engine (PT6A / T56 — V8 pipeline mapping)
 *   2. Shanghai SMT Maglev (Transrapid TR08 — 10 mm non-contact guideway)
 */
export const GROUPS: Array<{ name: string; machines: MachineDef[] }> = [
  { name: 'Powertrain', machines: [turboprop] },
  { name: 'Rail Transit', machines: [maglev] },
];

export const MACHINES: MachineDef[] = GROUPS.flatMap((g) => g.machines);

/** Every assembly, including the sub-assemblies reached through a part. */
const ALL: MachineDef[] = [...MACHINES, ...TURBOPROP_LEVELS, ...MAGLEV_LEVELS];

export const allMachines = () => ALL;

// For the scripts/ tools: every level the app really registers.
if (typeof window !== 'undefined') {
  (window as unknown as { gewu: unknown }).gewu = { assemblies: () => ALL.map((m) => ({ id: m.id, parent: m.parent ?? null })) };
}
export const hasMachine = (id: string) => ALL.some((m) => m.id === id);

export function machineById(id: string): MachineDef {
  return ALL.find((m) => m.id === id) ?? MACHINES[0];
}

/** The chain of assemblies from the top level down to this one. */
export function lineage(machine: MachineDef): MachineDef[] {
  const chain = [machine];
  while (chain[0].parent) chain.unshift(machineById(chain[0].parent));
  return chain;
}

/** The machine on the sheet right now (for non-React code: every frame and export). */
export function currentMachine(): MachineDef {
  return machineById(useStudio.getState().machineId);
}

export function useMachine(): MachineDef {
  return machineById(useStudio((s) => s.machineId));
}
