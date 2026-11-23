export type Vec2 = [number, number];
export type Vec3 = [number, number, number];

export type Tone = 'proved' | 'warn' | 'fail' | 'neutral';

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
