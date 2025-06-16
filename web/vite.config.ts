import { defineConfig } from 'vite'
export default defineConfig({
  root: 'web',
  base: '/gamemaker/',
  build: {
    outDir: '../dist',
    emptyOutDir: true,
  }
})