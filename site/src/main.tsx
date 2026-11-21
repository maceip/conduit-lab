import { createRoot } from 'react-dom/client';
import '@maceip/ix-workbench-primitives/styles.css';
import './site.css';
import App from './App';

createRoot(document.getElementById('root')!).render(<App />);