import React from 'react';

interface IconProps {
  size?: number;
  className?: string;
}

const base = (size: number, className?: string) => ({
  width: size,
  height: size,
  viewBox: '0 0 16 16',
  fill: 'none',
  stroke: 'currentColor',
  strokeWidth: 1.6,
  strokeLinecap: 'round' as const,
  strokeLinejoin: 'round' as const,
  'aria-hidden': true as const,
  className,
});

export const IconCheck: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M5.2 8.2 7.1 10.1 11 6.1" />
  </svg>
);

export const IconX: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M5.7 5.7 10.3 10.3M10.3 5.7 5.7 10.3" />
  </svg>
);

export const IconClock: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M8 4.7V8l2.4 1.5" />
  </svg>
);

export const IconShieldAlert: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M8 1.8 13.5 4v3.8c0 3.2-2.2 5.4-5.5 6.4C4.7 13.2 2.5 11 2.5 7.8V4L8 1.8Z" />
    <path d="M8 5.4v3.2M8 11.1h.01" />
  </svg>
);

export const IconCopy: React.FC<IconProps> = ({ size = 13, className }) => (
  <svg {...base(size, className)}>
    <rect x="5.5" y="5.5" width="8" height="8" rx="1.5" />
    <path d="M10.5 5.5V3.8A1.3 1.3 0 0 0 9.2 2.5H3.8A1.3 1.3 0 0 0 2.5 3.8v5.4a1.3 1.3 0 0 0 1.3 1.3h1.7" />
  </svg>
);

export const IconExternal: React.FC<IconProps> = ({ size = 12, className }) => (
  <svg {...base(size, className)}>
    <path d="M6.5 3.5H3.5a1 1 0 0 0-1 1v8a1 1 0 0 0 1 1h8a1 1 0 0 0 1-1v-3" />
    <path d="M9.2 2.5h4.3v4.3M13.5 2.5 7.5 8.5" />
  </svg>
);

export const IconChevron: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M6 4.2 10 8l-4 3.8" />
  </svg>
);

export const IconArrowDown: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M8 2.5v10.5M4.5 9.5 8 13l3.5-3.5" />
  </svg>
);

export const IconArrowRight: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M2.5 8h10.5M9.5 4.5 13 8l-3.5 3.5" />
  </svg>
);

export const IconGitHub: React.FC<IconProps> = ({ size = 16, className }) => (
  <svg
    width={size}
    height={size}
    viewBox="0 0 16 16"
    fill="currentColor"
    aria-hidden="true"
    className={className}
  >
    <path d="M8 0C3.58 0 0 3.58 0 8c0 3.54 2.29 6.53 5.47 7.59.4.07.55-.17.55-.38 0-.19-.01-.82-.01-1.49-2.01.37-2.53-.49-2.69-.94-.09-.23-.48-.94-.82-1.13-.28-.15-.68-.52-.01-.53.63-.01 1.08.58 1.23.82.72 1.21 1.87.87 2.33.66.07-.52.28-.87.51-1.07-1.78-.2-3.64-.89-3.64-3.95 0-.87.31-1.59.82-2.15-.08-.2-.36-1.02.08-2.12 0 0 .67-.21 2.2.82.64-.18 1.32-.27 2-.27s1.36.09 2 .27c1.53-1.04 2.2-.82 2.2-.82.44 1.1.16 1.92.08 2.12.51.56.82 1.27.82 2.15 0 3.07-1.87 3.75-3.65 3.95.29.25.54.73.54 1.48 0 1.07-.01 1.93-.01 2.2 0 .21.15.46.55.38A8.01 8.01 0 0 0 16 8c0-4.42-3.58-8-8-8Z" />
  </svg>
);
