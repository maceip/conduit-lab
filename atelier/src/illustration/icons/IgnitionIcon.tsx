import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { gear2D, projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * Bytecode dispatch loop.
 *
 * Source: `v8-iso/pages/fig-05-ignition.html`. That plate draws a horizontal
 * cylindrical starter motor barrel with radial cooling fins, a piggyback
 * solenoid with a copper jumper busbar, a meshing twelve-tooth starter pinion
 * against a large flywheel ring gear, a cylindrical common fuel rail with four
 * curved high-pressure lines feeding four stepped conical injectors, and a
 * cast intake runner tube below them.
 *
 * The pinion is a real toothed profile, extruded flat like the one in the
 * source figure.
 *
 * Tones: the ramp is applied within the part's own palette, exactly as the
 * published figures do it — `hi` for the prominent machined element, `dark`
 * for understructure, `body` for the main mass. Here: `hi` = solenoid, pinion; `dark` = motor, runner; the rest `body`.
 */
export const IGNITION_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [1, 0, 0],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'motor',
      label: 'Starter motor',
      palette: 'dark',
      balloon: 1,
      sectioned: true,
      geometry: { kind: 'cyl', from: [-170, 0, 0], to: [-40, 0, 0], r0: 36, r1: 36 },
    },
    {
      id: 'solenoid',
      label: 'Solenoid',
      palette: 'hi',
      balloon: 2,
      explode: [36, 0, 0],
      geometry: { kind: 'cyl', from: [-150, 0, 0], to: [-70, 0, 0], r0: 18, r1: 18 },
    },
    {
      id: 'pinion',
      label: 'Starter pinion',
      palette: 'hi',
      balloon: 3,
      explode: [72, 0, 0],
      geometry: {
        kind: 'extrude',
        poly: gear2D(10, 19, 26).map(([u, v]) => [u - 10, v] as [number, number]),
        depth: 14,
      },
    },
    {
      id: 'flywheel',
      label: 'Flywheel ring gear',
      palette: 'body',
      balloon: 4,
      explode: [108, 0, 0],
      geometry: { kind: 'cyl', from: [10, -38, 0], to: [10, -38, 22], r0: 44, r1: 44 },
    },
    {
      id: 'rail',
      label: 'Bytecode fuel rail',
      palette: 'body',
      balloon: 5,
      explode: [144, 0, 0],
      geometry: { kind: 'cyl', from: [-120, 36, 0], to: [-120, 36, 130], r0: 11, r1: 11 },
    },
    {
      id: 'injector',
      label: 'Injector',
      palette: 'body',
      balloon: 6,
      explode: [180, 0, 0],
      geometry: { kind: 'cyl', from: [40, 36, 0], to: [40, 36, 46], r0: 9, r1: 17 },
    },
    {
      id: 'runner',
      label: 'Intake runner',
      palette: 'dark',
      balloon: 7,
      explode: [216, 0, 0],
      geometry: { kind: 'cyl', from: [-140, 78, 0], to: [10, 78, 0], r0: 18, r1: 18 },
    },
  ],
};

export function IgnitionIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(IGNITION_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
