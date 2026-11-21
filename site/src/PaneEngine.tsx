import React from 'react';
import { IxBlind } from '@siemens/ix-react';
import {
  IxDigestBadge,
  IxPacketGrid,
  IxProofDag,
  type PacketGridColumn,
} from '@maceip/ix-workbench-primitives';
import {
  NR,
  crateOk,
  trustedTotal,
  blobUrl,
  type Ratchet,
  type Stats,
} from './data';
import { CVES, COVERAGE_LABEL, coverageTone } from './content/cves';
import { TRADEOFFS } from './content/tradeoffs';
import { VJS_STEPS, FUEL_THEOREM } from './content/vjs';
import { VURL_DAG_NODES, VURL_DAG_EDGES } from './content/vurl';
import { SectionHead, Stat, ShimDiagram, Source } from './parts';

const CVE_COLUMNS: PacketGridColumn[] = [
  { key: 'cve', label: 'CVE', mono: true, width: 1.35 },
  { key: 'patched', label: 'Patched', mono: true, width: 0.95 },
  { key: 'component', label: 'Component', width: 1 },
  { key: 'klass', label: 'Bug class', width: 1.35 },
  { key: 'coverageLabel', label: 'This engine’s answer', width: 1.5 },
];

const CVE_ROWS = CVES.map((c) => ({ ...c, coverageLabel: COVERAGE_LABEL[c.coverage] }));

const PaneEngine: React.FC<{ ratchet: Ratchet | null; stats: Stats | null }> = ({ ratchet, stats }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const ok = crateOk(vurl);
  const trusted = trustedTotal(vurl);
  const tally = {
    construction: CVES.filter((c) => c.coverage === 'construction').length,
    containment: CVES.filter((c) => c.coverage === 'containment').length,
    graphics: CVES.filter((c) => c.coverage === 'graphics').length,
  };

  return (
    <>
      <SectionHead index="03 · The ratchet" title="Where this engine actually stands">
        Phase 1 is real: <code>vurl</code>, the WHATWG URL standard transcribed into Verus and
        proved. Everything else on this pane is either measured from the latest run or explicitly
        marked as design. The ratchet never lets the verified share go down.
      </SectionHead>

      <div className="wb-stats" data-testid="ratchet-stats">
        <Stat value={vurl ? String(vurl.verified) : NR} label="verified functions" tone={ok ? 'verified' : 'critical'} />
        <Stat value={trusted === null ? NR : String(trusted)} label="trusted items" tone={trusted === 0 ? 'verified' : 'critical'} />
        <Stat value={vurl ? `${vurl.verify_seconds}s` : NR} label="re-verify time" />
        <Stat
          value={vurl ? `${vurl.tests_passed}/${vurl.tests_passed + vurl.tests_failed}` : NR}
          label="WPT + diff tests"
          tone={vurl && vurl.tests_failed === 0 ? 'verified' : 'critical'}
        />
      </div>

      <div className="wb-badge-row">
        <IxDigestBadge
          prefix="whatwg/url"
          digest="4f461b81a748443b235840599cea6290df40329a"
          tone="verified"
          statusLabel="spec pinned"
        />
        <IxDigestBadge
          prefix="verus"
          digest={ratchet?.verus ?? NR}
          tone={ratchet ? 'verified' : 'neutral'}
          statusLabel="upstream, not forked"
        />
        {stats?.toolchains?.z3 && (
          <IxDigestBadge
            prefix="z3"
            digest={(stats.toolchains.z3.match(/version ([\d.]+)/) ?? [null, stats.toolchains.z3])[1] ?? stats.toolchains.z3}
            tone="neutral"
            statusLabel="native arm64"
          />
        )}
      </div>

      <IxBlind
        label="Honesty clause: only vurl exists"
        sublabel="vjs is 0% built — every J-step below is design"
        variant="warning"
        collapsed={false}
      >
        <div className="wb-blind-body">
          The JS engine (<code>vjs</code>), the kernel theorems, and the Nanvix renderer isolation
          are <strong>design documents, not code</strong>. Until they land, this browser's V8-class
          protection equals whatever untrusted engine ships inside a not-yet-proven sandbox — the
          same bet Chrome makes today. The plan says so out loud, and the ratchet is the only
          progress number published.
        </div>
      </IxBlind>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>Proof obligation graph — vurl</div>
        {vurl ? (
          <div className="wb-dag-frame">
            <IxProofDag
              nodes={VURL_DAG_NODES.map((n) => ({ ...n, state: ok ? 'verified' : 'invalidated' }))}
              edges={VURL_DAG_EDGES}
              width={620}
              nodeWidth={160}
            />
          </div>
        ) : (
          <div className="wb-callout" data-tone="critical">
            Ratchet not loaded — the obligation graph is not drawn without real verification data.
          </div>
        )}
        <p className="wb-prose" style={{ marginTop: 8 }}>
          Click a node to see its downstream impact. Not yet modeled: validation errors,
          opaque/domain hosts, IDNA, the basic URL parser state machine. Not yet proved: the IPv6
          serialize→parse roundtrip (tested on 200k random addresses — tested, not proved).
        </p>
      </div>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>
          Does it cover the bugs that actually get exploited?
        </div>
        <p className="wb-prose" style={{ marginBottom: 10 }}>
          The last 20 Chrome CVEs confirmed exploited in the wild (as of 2026-11-20), each row
          checked against primary sources in the{' '}
          <Source href={blobUrl('docs/vjs-plan-review.md')}>plan review</Source>. V8 is 13 of 20.
        </p>
        <div className="wb-grid-frame">
          <IxPacketGrid
            columns={CVE_COLUMNS}
            rows={CVE_ROWS}
            unitLabel="CVEs"
            emptyLabel="No CVEs loaded"
            getRowTone={(row) => coverageTone(row.coverage as 'construction' | 'containment' | 'graphics')}
          />
        </div>
        <p className="wb-prose" style={{ marginTop: 8 }} data-testid="coverage-tally">
          <strong>{tally.construction}/20</strong> answered by construction once vjs is built
          (today: 0%) · <strong>{tally.containment}/20</strong> by the containment story, if the
          kernel theorems land · <strong>{tally.graphics}/20</strong> (Dawn, Skia, ANGLE) have no
          verified replacement planned — they are contained per-site, and the design says so.
        </p>
      </div>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>vjs — the end-to-end theorem</div>
        <pre className="wb-code" data-testid="fuel-theorem">{FUEL_THEOREM}</pre>
        <div className="wb-table-wrap" style={{ marginTop: 10 }}>
          <table className="wb-table" data-testid="vjs-table">
            <thead>
              <tr><th>Step</th><th>Scope</th><th>Exit criterion (measured)</th><th>Status</th></tr>
            </thead>
            <tbody>
              {VJS_STEPS.map((s) => (
                <tr key={s.step}>
                  <td className="mono">{s.step}</td>
                  <td>{s.scope}</td>
                  <td>{s.exit}</td>
                  <td className="mono">design</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>The tradeoffs, stated plainly</div>
        <div className="wb-table-wrap">
          <table className="wb-table" data-testid="tradeoffs-table">
            <thead>
              <tr><th>Decision</th><th>Given up</th><th>Gained</th><th>Residual risk</th></tr>
            </thead>
            <tbody>
              {TRADEOFFS.map((t, i) => (
                <tr key={i}>
                  <td>{t.decision}</td>
                  <td>{t.givenUp}</td>
                  <td>{t.gained}</td>
                  <td>{t.residual}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>The architecture the tradeoffs buy</div>
        <ShimDiagram />
      </div>

      <p className="wb-prose">
        Sources: <Source href={blobUrl('docs/verified-browser-engine.md')}>design doc</Source> ·{' '}
        <Source href={blobUrl('docs/vjs-plan-review.md')}>CVE coverage review</Source> ·{' '}
        <Source href={blobUrl('browser/README.md')}>vurl README</Source> ·{' '}
        <Source href="browser/ratchet.json">raw ratchet</Source> ·{' '}
        <Source href={blobUrl('browser/url/tests/data/PROVENANCE')}>WPT provenance</Source>
      </p>
    </>
  );
};

export default PaneEngine;