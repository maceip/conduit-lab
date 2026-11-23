export type Vec2 = [number, number];
export type Vec3 = [number, number, number];

export type Tone = 'proved' | 'warn' | 'fail' | 'neutral';

/**
 * Which published body palette a part is shaded from.
 *
 * The plates in `v8-iso/` are NOT drawn on one ramp. Each part selects a
 * palette and the shading ramp is applied within it, which is what gives them
 * their tonal range — a dark skid under a bright machined silo. Collapsing
 * every part onto a single ramp loses the form entirely.
 *
 * - `dark` — pedestals, frames, understructure (published `--dk0..--dk2`)
 * - `body` — the main mass (published `--bd0..--bd3`)
 * - `hi`   — the prominent machined element (published `--hi0..--hi3`)
 */
export type Palette = 'dark' | 'body' | 'hi';

export type GeometrySpec =
  | { kind: 'box'; at: Vec3; size: Vec3 }
  | { kind: 'cyl'; from: Vec3; to: Vec3; r0: number; r1?: number }
  | { kind: 'revolve'; profile: Vec2[]; segments: number }
  | { kind: 'loft'; stations: Vec3[] }
  | { kind: 'extrude'; poly: Vec2[]; depth: number }
  | { kind: 'tube'; points: Vec3[]; radius: number };

export interface Part {
  id: string;
  label: string;
  balloon?: number;
  explode?: Vec3;
  sectioned?: boolean;
  /** Body palette for this part's shading. Defaults to 'body'. */
  palette?: Palette;
  geometry: GeometrySpec;
}

export interface IconProps {
  size?: number;
  className?: string;
  tone?: Tone;
  annotated?: boolean;
  title?: string;
}

export interface PlateProps {
  className?: string;
  tone?: Tone;
  title?: string;
}
