import { defineConfig } from 'vite'
export default defineConfig({
  base: '/gamemaker/',
  build: {
    outDir: '../dist',
    emptyOutDir: true,
  }
})
