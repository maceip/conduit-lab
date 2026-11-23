import { StrictMode } from 'react';
import { createRoot } from 'react-dom/client';
import { App } from './App';
import { MotionProvider } from './contract/motion';

const host = document.getElementById('root');
if (!host) throw new Error('atelier: #root missing');

createRoot(host).render(
  <StrictMode>
    <MotionProvider>
      <App />
    </MotionProvider>
  </StrictMode>,
);
